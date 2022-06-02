#include "printf.h"

static volatile long *const print_data   = (volatile long *const) 0x20000;

void veri_putc(char c)
{
    *print_data = c;
}

void veri_write(int n, const char *buf)
{
    for ( ; n > 0; n--)
        veri_putc(*(buf++));
}

int veri_puts(const char *str)
{
    for ( ; *str != 0; str++)
        veri_putc(*str);

    return 1;
}

int veri_printf_unsigned(unsigned value, int width, char pad)
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
        veri_putc(pad);

    char* p = buffer + charCount - 1;
    for (int i = 0; i < charCount; ++i)
        veri_putc(*p--);

    return charCount;
}


int veri_printf_decimal(int value, int width, char pad)
{
    char buffer[20];
    int charCount = 0;

    unsigned neg = value < 0;
    if (neg)
        {
        value = -value;
        veri_putc('-');
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
        veri_putc(pad);

    char* p = buffer + charCount - 1;
    for (int i = 0; i < charCount; ++i)
        veri_putc(*p--);

    if (neg)
        charCount++;

    return charCount; 
}


int veri_printf_int(int value, int width, int pad, int base)
{
    if (base == 10)
        return veri_printf_decimal(value, width, pad);

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
        veri_putc(*p--);

    return charCount;
}

int veri_printf_impl(const char* format, va_list ap)
{
    int count = 0;  // Printed character count

    for (const char* fp = format; *fp; fp++)
        {
        char pad = ' ';
        int width = 0;  // Field width

        if (*fp != '%')
            {
            veri_putc(*fp);
            ++count;
            continue;
            }

        ++fp;  // Skip %

        if (*fp == 0)
            break;

        if (*fp == '%')
            {
            veri_putc('%');
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
            count += veri_printf_decimal(va_arg(ap, int), width, pad);
            break;

            case 'u':
            count += veri_printf_unsigned((unsigned) va_arg(ap, unsigned), width, pad);
            break;

            case 'x':
            case 'X':
            count += veri_printf_int(va_arg(ap, int), width, pad, 16);
            break;

            case 'o':
            count += veri_printf_int(va_arg(ap, int), width, pad, 8);
            break;

            case 'c':
            veri_putc(va_arg(ap, int));
            ++count;
            break;

            case 's':
            count += veri_puts(va_arg(ap, char*));
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

int printf(const char* format, ...)
{
  va_list ap;

  va_start(ap, format);
  int code = veri_printf_impl(format, ap);
  va_end(ap);

  return code;
}


