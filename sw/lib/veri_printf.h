#ifndef VERI_PRINTF_H
#define VERI_PRINTF_H

#include <stdarg.h>
#include <stdint.h>

void veri_putc(char c);

void veri_write(int n, const char *buf);

int veri_puts(const char *str);

int printf(const char* format, ...);

#endif
