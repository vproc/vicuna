#ifndef UART_H
#define UART_H

#include <stdarg.h>
#include <stdint.h>

void uart_putc(char c);
char uart_getc(void);

void uart_write(int n, const char *buf);
void uart_read(int n, char *buf);

int uart_puts(const char *str);
void uart_gets(char *buf, int size);

int uart_printf(const char* format, ...);

#endif
