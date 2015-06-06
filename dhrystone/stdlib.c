#include <stdarg.h>

extern long time();
extern long insn();
extern char *malloc();
extern void *memcpy(char *dest, const char *src, int n);
extern char *strcpy(char *dest, const char *src);
extern int strcmp(const char *s1, const char *s2);
extern int printf(const char *format, ...);
extern int scanf(const char *format, ...);

char heap_memory[1024];
int heap_memory_used = 0;

long time()
{
	int cycles;
	asm("rdcycle %0" : "=r"(cycles));
	// printf("[time() -> %d]", cycles);
	return cycles;
}

long insn()
{
	int insns;
	asm("rdinstret %0" : "=r"(insns));
	// printf("[insn() -> %d]", insns);
	return insns;
}

char *malloc(int size)
{
	char *p = heap_memory + heap_memory_used;
	// printf("[malloc(%d) -> %d (%d..%d)]", size, (int)p, heap_memory_used, heap_memory_used + size);
	heap_memory_used += size;
	if (heap_memory_used > 1024)
		asm("sbreak");
	return p;
}

void *memcpy(char *dest, const char *src, int n)
{
	while (n--)
		*(dest++) = *(src++);
}

char *strcpy(char *dest, const char *src)
{
	char *ret = dest;
	// printf("[strcpy()]");
	do
		*(dest++) = *src;
	while (*(src++));
	return ret;
}

int strcmp(const char *s1, const char *s2)
{
	// printf("[strcmp()]");
	while (1) {
		if (*s1 == 0 && *s2 == 0)
			return 0;
		if (*s1 < *s2)
			return -1;
		if (*s1 > *s2)
			return +1;
		s1++, s2++;
	}
}

static void printf_c(int c)
{
	*((volatile int*)0x10000000) = c;
}

static void printf_s(char *p)
{
	while (*p)
		*((volatile int*)0x10000000) = *(p++);
}

static void printf_d(int val)
{
	char buffer[32];
	char *p = buffer;
	if (val < 0) {
		printf_c('-');
		val = -val;
	}
	while (val || p == buffer) {
		*(p++) = '0' + val % 10;
		val = val / 10;
	}
	while (p != buffer)
		printf_c(*(--p));
}

int printf(const char *format, ...)
{
	int i;
	va_list ap;

	va_start(ap, format);

	for (i = 0; format[i]; i++)
		if (format[i] == '%') {
			while (format[++i]) {
				if (format[i] == 'c') {
					printf_c(va_arg(ap,int));
					break;
				}
				if (format[i] == 's') {
					printf_s(va_arg(ap,char*));
					break;
				}
				if (format[i] == 'd') {
					printf_d(va_arg(ap,int));
					break;
				}
			}
		} else
			printf_c(format[i]);

	va_end(ap);
}

int scanf(const char *format, ...)
{
	// printf("[scanf(\"%s\")]\n", format);
	va_list ap;
	va_start(ap, format);
	*va_arg(ap,int*) = 100;
	va_end(ap);
	return 0;
}

