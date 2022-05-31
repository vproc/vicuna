#include "runtime.h"

// Function to read cpu mcycle csr for performance measurements
uint64_t get_mcycle(){
    unsigned int mcyclel;
    unsigned int mcycleh0 = 0, mcycleh1=1;
    uint64_t cycles;

    while(mcycleh0 != mcycleh1) {
        asm volatile ("csrr %0,mcycleh"  : "=r" (mcycleh0) );
        asm volatile ("csrr %0,mcycle"   : "=r" (mcyclel)  );
        asm volatile ("csrr %0,mcycleh"  : "=r" (mcycleh1) );
    }
    cycles = mcycleh1;
    return (cycles << 32) | mcyclel;
}