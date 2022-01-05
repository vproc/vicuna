#include "uart.h"

static volatile long *const uart_data   = (volatile long *const) 0xFF000000;
static volatile long *const uart_status = (volatile long *const) 0xFF000004;

void uart_putc(char c)
{
    // wait until transmitter ready:
    while (((*uart_status) & 1))
        ;
    *uart_data = c;
}

char uart_getc(void)
{
    int data;
    // wait until a character was received:
    while ((data = *uart_data) < 0)
        ;
    return data;
}

void uart_write(int n, const char *buf)
{
    for ( ; n > 0; n--)
        uart_putc(*(buf++));
}

void uart_read(int n, char *buf)
{
    for ( ; n > 0; n--)
        *(buf++) = uart_getc();
}

void uart_puts(const char *str)
{
    for ( ; *str != 0; str++)
        uart_putc(*str);
}

void uart_gets(char *buf, int size)
{
    char c = 0;
    for ( ; size > 1 && c != '\n' && c != '\r'; size--)
        *(buf++) = c = uart_getc();
    *buf = 0;
}
