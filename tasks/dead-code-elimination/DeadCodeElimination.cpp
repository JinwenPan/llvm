/*
Refenrence:
https://llvm.org/doxygen/DCE_8cpp_source.html
https://db.in.tum.de/teaching/ws2324/codegen/ex05.txt?lang=en
https://github.com/abhandaru/cs745-llvm-src/blob/master/ClassicalDataflow/dead-code-elimination.cpp
https://stackoverflow.com/questions/21708209/get-predecessors-for-basicblock-in-llvm
https://zhuanlan.zhihu.com/p/571598830
https://csstormq.github.io/blog/LLVM%20%E4%B9%8B%20IR%20%E7%AF%87%EF%BC%886%EF%BC%89%EF%BC%9A%E5%A6%82%E4%BD%95%E7%BC%96%E5%86%99%E6%B6%88%E9%99%A4%E6%AD%BB%E4%BB%A3%E7%A0%81%20Pass
LLVM Cookbook: Mayur Pandey and Suyog Sarda, Page 132
This implementation mainly refers to the book above, especially the part of trivially dead instructions elimination
*/

#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SmallPtrSet.h"

#define DEBUG_TYPE "remove-dead-code"

using namespace llvm;

namespace {
    struct DeadCodeEliminationPass : PassInfoMixin<DeadCodeEliminationPass> {
        PreservedAnalyses run(Function &Func, FunctionAnalysisManager &AnalysisMgr) {
            auto EliminateUselessBranches = [](BasicBlock &Block, PostDominatorTree &PostDomTree, bool &ChangesMade) {
                SmallVector<BranchInst *, 16> RedundantBranches;

                for (auto &Instr : Block) {
                    if (auto *BranchInstr = dyn_cast<BranchInst>(&Instr)) {
                        if (BranchInstr->isConditional()) {
                            bool IdenticalTargets = true;
                            for (auto *Successor : successors(BranchInstr->getParent())) {
                                if (Successor != BranchInstr->getSuccessor(0)) {
                                    IdenticalTargets = false;
                                    break;
                                }
                            }
                            if (IdenticalTargets) {
                                RedundantBranches.push_back(BranchInstr);
                            }
                        }
                    }
                }

                for (BranchInst *BranchInstr : RedundantBranches) {
                    ChangesMade = true;
                    auto *Successor = BranchInstr->getSuccessor(0);
                    auto *UnconditionalBranch = BranchInst::Create(Successor, BranchInstr->getParent());
                    BranchInstr->eraseFromParent();
                }
            };

            auto EliminateDeadInstructions = [](BasicBlock &Block, PostDominatorTree &PostDomTree, bool &ChangesMade, unsigned &RemovedInstrCount) {
                SmallVector<WeakTrackingVH, 16> DeadInstructions;

                for (auto &Instr : Block) {
                    if (isInstructionTriviallyDead(&Instr)) {
                        DeadInstructions.push_back(&Instr);
                    } else if (auto *StoreInstr = dyn_cast<StoreInst>(&Instr); StoreInstr && !StoreInstr->isVolatile()) {
                        auto PointerOperand = StoreInstr->getOperand(1);
                        while (auto *Operand = dyn_cast<BitCastInst>(PointerOperand)) {
                            PointerOperand = Operand;
                        }

                        if (dyn_cast<AllocaInst>(PointerOperand)) {
                            bool DominatedByStore = true;
                            for (auto UserIt = PointerOperand->user_begin(); UserIt != PointerOperand->user_end(); ++UserIt) {
                                DominatedByStore &= PostDomTree.dominates(StoreInstr, static_cast<Instruction *>(*UserIt));
                            }
                            if (DominatedByStore) {
                                DeadInstructions.push_back(StoreInstr);
                            }
                        }
                    }
                }

                RecursivelyDeleteTriviallyDeadInstructions(
                    DeadInstructions, nullptr, nullptr,
                    [&ChangesMade, &RemovedInstrCount](Value *Val) {
                        ChangesMade = true;
                        ++RemovedInstrCount;
                    });
            };

            auto RemoveRedundantBlocks = [](std::vector<BasicBlock *> &BlockList, bool &ChangesMade) {
                for (auto *Block : BlockList) {
                    if (Block->size() != 1 || !isa<BranchInst>(Block->getTerminator())) {
                        continue;
                    }

                    auto *BranchInstr = dyn_cast<BranchInst>(Block->getTerminator());
                    if (!BranchInstr->isUnconditional()) {
                        continue;
                    }

                    ChangesMade = true;

                    auto *Successor = BranchInstr->getSuccessor(0);
                    for (auto *Predecessor : predecessors(Block)) {
                        Predecessor->getTerminator()->replaceUsesOfWith(Block, Successor);
                    }

                    Block->eraseFromParent();
                }
            };

            bool ChangesMade = true;

            unsigned RemovedInstrCount = 0;

            while (ChangesMade) {
                ChangesMade = false;
                std::vector<BasicBlock *> BlockList;
                PostDominatorTree PostDomTree(Func);

                for (auto &Block : Func) {
                    BlockList.push_back(&Block);
                    EliminateDeadInstructions(Block, PostDomTree, ChangesMade, RemovedInstrCount);
                    EliminateUselessBranches(Block, PostDomTree, ChangesMade);
                }

                RemoveRedundantBlocks(BlockList, ChangesMade);
            }

            errs() << Func.getName() << ": Removed " << RemovedInstrCount << " instructions\n";

            return PreservedAnalyses::none();
        }

    };
} // namespace

/// Registration
PassPluginLibraryInfo getPassPluginInfo() {
    const auto callback = [](PassBuilder &PB) {
        PB.registerPipelineParsingCallback(
                [](StringRef Name, FunctionPassManager &FPM, auto) {
                    if (Name == "dead-code-elimination") {
                        FPM.addPass(DeadCodeEliminationPass());
                        return true;
                    }
                    return false;
                });
    };
    return {LLVM_PLUGIN_API_VERSION, "DeadCodeEliminationPass",
            LLVM_VERSION_STRING, callback};
};

extern "C" LLVM_ATTRIBUTE_WEAK PassPluginLibraryInfo llvmGetPassPluginInfo() {
    return getPassPluginInfo();
}

#undef DEBUG_TYPE