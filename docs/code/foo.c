#include <uart.h>

int main(void) {
    uart_printf("foo\n");
    asm volatile("jr x0"); // jump to address 0 (ends simulation)
    return 0;
}
