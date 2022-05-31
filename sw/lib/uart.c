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

int uart_puts(const char *str)
{
    for ( ; *str != 0; str++)
        uart_putc(*str);

    return 1;
}

void uart_gets(char *buf, int size)
{
    char c = 0;
    for ( ; size > 1 && c != '\n' && c != '\r'; size--)
        *(buf++) = c = uart_getc();
    *buf = 0;
}

int print_unsigned(unsigned value, int width, char pad)
{
    char buffer[20];
    int charCount = 0;

    do
    {
      char c = '0' + (value % 10);
      value = value / 10;
      buffer[charCount++] = c;
    }
    while (value);

    for (int i = charCount; i < width; ++i)
        uart_putc(pad);

    char* p = buffer + charCount - 1;
    for (int i = 0; i < charCount; ++i)
        uart_putc(*p--);

    return charCount;
}


int print_decimal(int value, int width, char pad)
{
    char buffer[20];
    int charCount = 0;

    unsigned neg = value < 0;
    if (neg)
        {
        value = -value;
        uart_putc('-');
        width--;
        }

    do
        {
        char c = '0' + (value % 10);
        value = value / 10;
        buffer[charCount++] = c;
        }
    while (value);

    for (int i = charCount; i < width; ++i)
        uart_putc(pad);

    char* p = buffer + charCount - 1;
    for (int i = 0; i < charCount; ++i)
        uart_putc(*p--);

    if (neg)
        charCount++;

    return charCount; 
}


int print_int(int value, int width, int pad, int base)
{
    if (base == 10)
        return print_decimal(value, width, pad);

    char buffer[20];
    int charCount = 0;

    unsigned uu = value;

    if (base == 8)
        {
        do
            {
            char c = '0' + (uu & 7);
            buffer[charCount++] = c;
            uu >>= 3;
            }
        while (uu);
        }
    else if (base == 16)
        {
        do
            {
            int digit = uu & 0xf;
            char c = digit < 10 ? '0' + digit : 'a' + digit - 10;
            buffer[charCount++] = c;
            uu >>= 4;
            }
        while (uu);
        }
    else
        return -1;

    char* p = buffer + charCount - 1;
    for (unsigned i = 0; i < charCount; ++i)
        uart_putc(*p--);

    return charCount;
}

int printf_impl(const char* format, va_list ap)
{
    int count = 0;  // Printed character count

    for (const char* fp = format; *fp; fp++)
        {
        char pad = ' ';
        int width = 0;  // Field width

        if (*fp != '%')
            {
            uart_putc(*fp);
            ++count;
            continue;
            }

        ++fp;  // Skip %

        if (*fp == 0)
            break;

        if (*fp == '%')
            {
            uart_putc('%');
            continue;
            }

        while (*fp == '0')
            {
            pad = '0';
            fp++;  // Pad zero not yet implented.
            }

        if (*fp == '-')
            {
            fp++;  // Pad right not yet implemented.
            }

        if (*fp == '*')
            {
            //int outWidth = va_arg(ap, int);
            fp++;  // Width not yet implemented.
            }
        else if (*fp >= '0' && *fp <= '9')
            {    // Width not yet implemented.
            while (*fp >= '0' && *fp <= '9')
                width = width * 10 + (*fp++ - '0');
            }

        switch (*fp)
            {
            case 'd':
            count += print_decimal(va_arg(ap, int), width, pad);
            break;

            case 'u':
            count += print_unsigned((unsigned) va_arg(ap, unsigned), width, pad);
            break;

            case 'x':
            case 'X':
            count += print_int(va_arg(ap, int), width, pad, 16);
            break;

            case 'o':
            count += print_int(va_arg(ap, int), width, pad, 8);
            break;

            case 'c':
            uart_putc(va_arg(ap, int));
            ++count;
            break;

            case 's':
            count += uart_puts(va_arg(ap, char*));
            break;
    /*
            case 'g':
            count += whisperPrintDoubleG(va_arg(ap, double));
            break;
            case 'f':
            count += whisperPrintDoubleF(va_arg(ap, double));
    */
            }
    }

  return count;
}

int uart_printf(const char* format, ...)
{
  va_list ap;

  va_start(ap, format);
  int code = printf_impl(format, ap);
  va_end(ap);

  return code;
}


