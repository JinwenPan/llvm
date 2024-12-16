/*
Reference:
https://stackoverflow.com/questions/24331498/llvm-insert-function-call-defined-from-another-file
https://www.cs.cornell.edu/courses/cs6120/2019fa/blog/mempass/
https://mukulrathi.com/create-your-own-programming-language/concurrency-runtime-language-tutorial/
https://stackoverflow.com/questions/42426774/how-to-determine-the-size-of-memory-a-particular-load-store-is-accessing-in-llvm
https://github.com/google/sanitizers/wiki/AddressSanitizerAlgorithm
https://stackoverflow.com/questions/17297109/create-new-function-in-llvm
https://llvm.org/docs/ProgrammersManual.html#the-isa-cast-and-dyn-cast-templates
https://llvm.org/docs/GetElementPtr.html
https://stackoverflow.com/questions/33327097/llvm-irbuilder-set-insert-point-after-a-particular-instruction
https://stackoverflow.com/questions/44034192/how-to-get-the-next-immediate-instruction-for-a-given-instruction
https://stackoverflow.com/questions/73020963/what-is-the-difference-between-llvmcallbasegetargoperand-and-llvmunaryin
AddressSanitizer: A Fast Address Sanity Checker: Konstantin Serebryany, Derek Bruening, Alexander Potapenko, Dmitry Vyukov
This implementation mainly refers to the ASan paper above, including mapping, checking, instrumentation, shadow memory configurations, etc. 
*/

#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Value.h"
#include "llvm/Pass.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/DerivedTypes.h"

#define DEBUG_TYPE "memory-safety"

using namespace llvm;

namespace {
    struct MemorySafetyPass : PassInfoMixin<MemorySafetyPass>, public InstVisitor<MemorySafetyPass> {
    public:
        PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM) {
            errs() << "Running MemorySafetyPass on function " << F.getName() << "\n";
            if (F.getName() == "main") initializeShadow(F);
            this->visit(F);
            return PreservedAnalyses::all();
        }

        void initializeShadow(Function &F){
            Module* M = F.getParent();
            LLVMContext& C = M->getContext();
            FunctionType* initFuncType = FunctionType::get(Type::getVoidTy(C), false);
            FunctionCallee initFuncCallee = M->getOrInsertFunction("__runtime_init", initFuncType);
            Function* initFunc = cast<Function>(initFuncCallee.getCallee());
            BasicBlock& entry = F.getEntryBlock();
            IRBuilder<> B(&entry, entry.begin());
            B.CreateCall(initFunc); 
        }

        void visitAllocaInst(AllocaInst &I) {
            Function* F = I.getParent()->getParent();
            Module* M = F->getParent();
            LLVMContext& C = M->getContext();
            const DataLayout& DL = M->getDataLayout();

            // replace old alloca (and insert addroffset compute)
            Type* allocaType = I.getAllocatedType();
            uint64_t allocaSize = DL.getTypeAllocSize(allocaType);
            IRBuilder<> B(&I);
            Type* newAllocaType = ArrayType::get(Type::getInt8Ty(C), 64 + ((allocaSize + 31) & ~31));
            AllocaInst* AI = B.CreateAlloca(newAllocaType);
            Align align32 = Align(32);
            AI->setAlignment(align32);
            Value* addrOffset = ConstantInt::get(Type::getInt64Ty(C), 32);
            Value* newAddr = B.CreateGEP(Type::getInt8Ty(C), AI, addrOffset);
            I.replaceAllUsesWith(newAddr);
            I.eraseFromParent();

            // compute shadow
            Type* voidPtr = Type::getInt8PtrTy(C);
            FunctionType* getShadowFuncType = FunctionType::get(voidPtr, voidPtr, false);
            FunctionCallee getShadowFuncCallee = M->getOrInsertFunction("getShadowAddr", getShadowFuncType);
            Function* getShadowFunc = cast<Function>(getShadowFuncCallee.getCallee());
            IRBuilder<> getShadowB(AI->getNextNode()->getNextNode());
            CallInst* CI = getShadowB.CreateCall(getShadowFunc, AI);
            
            // poison lower redzone
            IRBuilder<> storeB(CI->getNextNode());
            Value* poisonInt = ConstantInt::get(Type::getInt32Ty(C), -1);
            storeB.CreateStore(poisonInt, CI);
            
            // unpoison pure payload
            uint64_t numOfCleanShadowBytes = allocaSize / 8;
            Value* unpoisonChar = ConstantInt::get(Type::getInt8Ty(C), 0);
            for (uint64_t i = 0; i < numOfCleanShadowBytes; i++) {
                Value* payloadOffset = ConstantInt::get(Type::getInt64Ty(C), i + 4);
                Value* payloadAddr = storeB.CreateGEP(Type::getInt8Ty(C), CI, payloadOffset);
                storeB.CreateStore(unpoisonChar, payloadAddr);
            }

            // partially poison payload
            uint64_t k = allocaSize % 8;
            if (k != 0){
                Value* kChar = ConstantInt::get(Type::getInt8Ty(C), (char)k);
                Value* offset = ConstantInt::get(Type::getInt64Ty(C), numOfCleanShadowBytes + 4);
                Value* offsetAddr = storeB.CreateGEP(Type::getInt8Ty(C), CI, offset);
                storeB.CreateStore(kChar, offsetAddr);
            }

            // poison pad
            uint64_t paddingSize = ((allocaSize + 31) & ~31) - allocaSize;
            uint64_t numOfPoisonShadowBytes = paddingSize / 8;
            Value* poisonChar = ConstantInt::get(Type::getInt8Ty(C), -1);
            for (uint64_t i = 0; i < numOfPoisonShadowBytes; i++) {
                Value* paddingOffset = ConstantInt::get(Type::getInt64Ty(C), i + numOfCleanShadowBytes + (k == 0 ? 4 : 5));
                Value* paddingAddr = storeB.CreateGEP(Type::getInt8Ty(C), CI, paddingOffset);
                storeB.CreateStore(poisonChar, paddingAddr);
            }

            // poison higher redzone
            Value* higherOffset = ConstantInt::get(Type::getInt64Ty(C), ((allocaSize + 31) & ~31) / 8 + 4);
            Value* higherOffsetAddr = storeB.CreateGEP(Type::getInt8Ty(C), CI, higherOffset);
            storeB.CreateStore(poisonInt, higherOffsetAddr);
        }

        void visitCallInst(CallInst &I) {
            Function* F = I.getParent()->getParent();
            Module* M = F->getParent();
            LLVMContext& C = M->getContext();

            if (I.getCalledFunction() && I.getCalledFunction()->getName() == "malloc") {
                Type* voidPtr = I.getType();
                Type* sizet = I.getArgOperand(0)->getType();
                FunctionType* mallocFuncType = FunctionType::get(voidPtr, sizet, false);
                FunctionCallee mallocFuncCallee = M->getOrInsertFunction("__runtime_malloc", mallocFuncType);
                Function *mallocFunc = cast<Function>(mallocFuncCallee.getCallee());
                IRBuilder<> B(&I);
                CallInst* CI = B.CreateCall(mallocFunc, I.getArgOperand(0));
                I.replaceAllUsesWith(CI);
                I.eraseFromParent();
            }
            else if (I.getCalledFunction() && I.getCalledFunction()->getName() == "free"){
                Type* voidPtr = I.getArgOperand(0)->getType();  
                FunctionType* freeFuncType = FunctionType::get(Type::getVoidTy(C), voidPtr, false);
                FunctionCallee freeFuncCallee = M->getOrInsertFunction("__runtime_free", freeFuncType);
                Function* freeFunc = cast<Function>(freeFuncCallee.getCallee());
                IRBuilder<> B(&I);
                B.CreateCall(freeFunc, I.getArgOperand(0));
                I.eraseFromParent();
            }
        }

        void visitLoadInst(LoadInst &I) {
            Function* F = I.getParent()->getParent();
            Module* M = F->getParent();
            LLVMContext& C = M->getContext();
            const DataLayout& DL = M->getDataLayout();

            Type* voidPtr = I.getPointerOperand()->getType();
            IntegerType* sizet = IntegerType::getInt64Ty(C);
            FunctionType* loadCheckFuncType = FunctionType::get(Type::getVoidTy(C), {voidPtr, sizet}, false);
            FunctionCallee loadCheckFuncCallee = M->getOrInsertFunction("__runtime_load_check_addr", loadCheckFuncType);
            Function* loadCheckFunc = cast<Function>(loadCheckFuncCallee.getCallee());
            IRBuilder<> B(&I);
            Value* addr = I.getPointerOperand();
            Type* loadType = I.getType();
            uint64_t loadSize = DL.getTypeAllocSize(loadType);
            Value* size = B.getInt64(loadSize);
            B.CreateCall(loadCheckFunc, {addr, size});
        }

        void visitStoreInst(StoreInst &I) {
            Function* F = I.getParent()->getParent();
            Module* M = F->getParent();
            LLVMContext& C = M->getContext();
            const DataLayout& DL = M->getDataLayout();

            Type* voidPtr = I.getPointerOperand()->getType();
            IntegerType* sizet = IntegerType::getInt64Ty(C);
            FunctionType *storeCheckFuncType = FunctionType::get(Type::getVoidTy(C), {voidPtr, sizet}, false);
            FunctionCallee storeCheckFuncCallee = M->getOrInsertFunction("__runtime_store_check_addr", storeCheckFuncType);
            Function* storeCheckFunc = cast<Function>(storeCheckFuncCallee.getCallee());
            IRBuilder<> B(&I);
            Value* addr = I.getPointerOperand();
            Type* storedType = I.getOperand(0)->getType();
            uint64_t storedSize = DL.getTypeAllocSize(storedType);
            Value* size = B.getInt64(storedSize);
            B.CreateCall(storeCheckFunc, {addr, size});
        }

        // do not skip this pass for functions annotated with optnone
        static bool isRequired() { return true; }
    };
} // namespace

/// Registration
PassPluginLibraryInfo getPassPluginInfo() {
    const auto callback = [](PassBuilder &PB) {
        PB.registerPipelineParsingCallback(
                [](StringRef Name, FunctionPassManager &FPM, auto) {
                    if (Name == "memory-safety") {
                        FPM.addPass(MemorySafetyPass());
                        return true;
                    }
                    return false;
                });
    };
    return {LLVM_PLUGIN_API_VERSION, "MemorySafetyPass",
            LLVM_VERSION_STRING, callback};
};

extern "C" LLVM_ATTRIBUTE_WEAK PassPluginLibraryInfo llvmGetPassPluginInfo() {
    return getPassPluginInfo();
}

#undef DEBUG_TYPE