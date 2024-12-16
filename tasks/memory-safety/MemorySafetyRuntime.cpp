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

#pragma clang diagnostic push
#pragma ide diagnostic ignored "bugprone-reserved-identifier"
/// The code in this file is just a skeleton. You are allowed (and encouraged!)
/// to change if it doesn't fit your needs or ideas.

#include <cstdlib>
#include <cstdio>
#include <cstdint>
#include <sys/mman.h>
#include <cstring>

void* const shadowStart = (void*)0x00007fff8000;
const size_t shadowSize = 0x100000000000; // include gap size
void* const shadowGapStart = (void*)0x00008fff7000;
const size_t shadowGapSize = 0x020000000000;
const uintptr_t shadowOffset = 0x00007fff8000;

const size_t redZoneSize = 16;
const int8_t isClean = 0;
const int8_t isRedZone = -1;
const int8_t isFreed = -2;

extern "C" {

__attribute__((used))
void* getShadowAddr(void* addr) {
    return (void*)(((uintptr_t)addr >> 3) + shadowOffset);
}

__attribute__((used))
void __runtime_init() {
    mmap(shadowStart, shadowSize, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE | MAP_FIXED, -1, 0);
}

__attribute__((used))
void __runtime_load_check_addr(void* addr, size_t size) {
    void* shadowAddr = getShadowAddr(addr);
    int8_t* k = (int8_t*)shadowAddr; 
    if (*k){
        int kNeeded = ((uintptr_t)addr & 7) + size;
        if (kNeeded > (int)*k){
            fprintf(stderr, "Illegal memory access\n");
            exit(1);
        }
    }
}

__attribute__((used))
void __runtime_store_check_addr(void* addr, size_t size) {
    void* shadowAddr = getShadowAddr(addr);
    int8_t* k = (int8_t*)shadowAddr; 
    if (*k){
        int kNeeded = ((uintptr_t)addr & 7) + size;
        if (kNeeded > (int)*k){
            fprintf(stderr, "Illegal memory access\n");
            exit(1);
        }
    }
}

__attribute__((used))
void *__runtime_malloc(size_t size) {
    void* addr = malloc(((size + 7) & ~7) + 2 * redZoneSize);

    // header
    size_t* mallocSize = (size_t*)addr;
    *mallocSize = size;

    // lower pad
    memset(getShadowAddr(addr), isRedZone, 2);
    
    // mid
    void* payloadAddr = (char*)addr + redZoneSize;
    memset(getShadowAddr(payloadAddr), isClean, (size >> 3)); // (size >> 3) == (size / 8);

    // higher pad (with unfilled mid maybe)
    size_t k = size & 7; // (size & 7) == (size % 8);
    if (k != 0){
        memset(getShadowAddr((char*)payloadAddr + (size & ~7)), (int8_t)k, 1); // (size & ~7) gets largest multiple of 8 but less than size
        memset(getShadowAddr((char*)payloadAddr + (size & ~7) + 8), isRedZone, 2); 
    }
    else{
        memset(getShadowAddr((char*)payloadAddr + size), isRedZone, 2);
    }

    return payloadAddr;
}

__attribute__((used))
void __runtime_free(void *ptr) {
    void* addr = (char*)ptr - redZoneSize;
    size_t* mallocSize = (size_t*)addr;
    memset(getShadowAddr(addr), isFreed, 4 + ((((*mallocSize) + 7) & ~7) >> 3));
    free(addr);
}

}

#pragma clang diagnostic pop