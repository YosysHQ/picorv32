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

#if 0
void *memcpy(char *dest, const char *src, int n)
{
	while (n--)
		*(dest++) = *(src++);
}
#else
/* copy&paste from disassembled libc */
asm (
"               .global memcpy;      "
"  memcpy:      xor     a5,a1,a0;    "
"               slli    a4,a5,0x1e;  "
"               add     a7,a0,a2;    "
"               bnez    a4,.M1;      "
"               li      a5,3;        "
"               bleu    a2,a5,.M2;   "
"               slli    a5,a0,0x1e;  "
"               bnez    a5,.M3;      "
"               andi    a6,a7,-4;    "
"               addi    a5,a6,-32;   "
"               mv      a4,a0;       "
"               bltu    a0,a5,.M4;   "
"  .M9:         mv      a3,a1;       "
"               mv      a5,a4;       "
"               bleu    a6,a4,.M5;   "
"  .M6:         lw      a2,0(a3);    "
"               addi    a5,a5,4;     "
"               addi    a3,a3,4;     "
"               sw      a2,-4(a5);   "
"               bltu    a5,a6,.M6;   "
"               not     a5,a4;       "
"               add     a6,a5,a6;    "
"               andi    a6,a6,-4;    "
"               addi    a6,a6,4;     "
"               add     a4,a4,a6;    "
"               add     a1,a1,a6;    "
"  .M5:         bltu    a4,a7,.M7;   "
"  .M11:        ret;                 "
"  .M3:         mv      a4,a0;       "
"  .M8:         lbu     a5,0(a1);    "
"               addi    a4,a4,1;     "
"               addi    a1,a1,1;     "
"               sb      a5,-1(a4);   "
"               slli    a5,a4,0x1e;  "
"               bnez    a5,.M8;      "
"               andi    a6,a7,-4;    "
"               addi    a5,a6,-32;   "
"               bleu    a5,a4,.M9;   "
"  .M4:         lw      t6,0(a1);    "
"               lw      t5,4(a1);    "
"               lw      t4,8(a1);    "
"               lw      t3,12(a1);   "
"               lw      t2,16(a1);   "
"               lw      t1,20(a1);   "
"               lw      t0,24(a1);   "
"               lw      a2,28(a1);   "
"               addi    a1,a1,36;    "
"               addi    a4,a4,36;    "
"               lw      a3,-4(a1);   "
"               sw      t6,-36(a4);  "
"               sw      t5,-32(a4);  "
"               sw      t4,-28(a4);  "
"               sw      t3,-24(a4);  "
"               sw      t2,-20(a4);  "
"               sw      t1,-16(a4);  "
"               sw      t0,-12(a4);  "
"               sw      a2,-8(a4);   "
"               sw      a3,-4(a4);   "
"               bltu    a4,a5,.M4;   "
"               j       .M9;         "
"  .M1:         mv      a4,a0;       "
"               bleu    a7,a0,.M10;  "
"  .M7:         lbu     a5,0(a1);    "
"               addi    a4,a4,1;     "
"               addi    a1,a1,1;     "
"               sb      a5,-1(a4);   "
"               bltu    a4,a7,.M7;   "
"  .M12:        ret;                 "
"  .M2:         mv      a4,a0;       "
"               bleu    a7,a0,.M11;  "
"               lbu     a5,0(a1);    "
"               addi    a4,a4,1;     "
"               addi    a1,a1,1;     "
"               sb      a5,-1(a4);   "
"               bltu    a4,a7,.M7;   "
"               j       .M12;        "
"  .M10:        ret;                 "
);
#endif

#if 0
char *strcpy(char *dest, const char *src)
{
	char *ret = dest;
	// printf("[strcpy()]");
	do
		*(dest++) = *src;
	while (*(src++));
	return ret;
}
#else
/* copy&paste from disassembled libc */
asm (
"               .global strcpy;      "
"  strcpy:      or      a5,a0,a1;    "
"               slli    a4,a5,0x1e;  "
"               bnez    a4,.S1;      "
"               lw      a4,0(a1);    "
"               lui     a3,0x7f7f8;  "
"               addi    a3,a3,-129;  "
"               and     a5,a4,a3;    "
"               add     a5,a5,a3;    "
"               or      a7,a4,a3;    "
"               or      a7,a7,a5;    "
"               li      a5,-1;       "
"               mv      a2,a0;       "
"               bne     a7,a5,.S2;   "
"  .S3:         addi    a2,a2,4;     "
"               addi    a1,a1,4;     "
"               sw      a4,-4(a2);   "
"               lw      a4,0(a1);    "
"               and     a5,a4,a3;    "
"               or      a6,a4,a3;    "
"               add     a5,a5,a3;    "
"               or      a5,a6,a5;    "
"               beq     a5,a7,.S3;   "
"  .S2:         lbu     a5,0(a1);    "
"               lbu     a4,1(a1);    "
"               lbu     a3,2(a1);    "
"               sb      a5,0(a2);    "
"               beqz    a5,.S4;      "
"               sb      a4,1(a2);    "
"               beqz    a4,.S4;      "
"               sb      a3,2(a2);    "
"               bnez    a3,.S5;      "
"  .S4:         ret;                 "
"  .S5:         sb      zero,3(a2);  "
"               ret;                 "
"  .S1:         mv      a5,a0;       "
"  .S6:         lbu     a4,0(a1);    "
"               addi    a5,a5,1;     "
"               addi    a1,a1,1;     "
"               sb      a4,-1(a5);   "
"               bnez    a4,.S6;      "
"               ret;                 "
);
#endif

#if 0
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
#else
/* copy&paste from disassembled libc */
asm (
"               .global strcmp;      "
"  strcmp:      or      a4,a0,a1;    "
"               li      t2,-1;       "
"               andi    a4,a4,3;     "
"               bnez    a4,.K1;      "
"               lui     t3,0x7f7f8;  "
"               addi    t3,t3,-129;  "
"  .K6:         lw      a2,0(a0);    "
"               lw      a3,0(a1);    "
"               and     t0,a2,t3;    "
"               or      t1,a2,t3;    "
"               add     t0,t0,t3;    "
"               or      t0,t0,t1;    "
"               bne     t0,t2,.K2;   "
"               bne     a2,a3,.K3;   "
"               lw      a2,4(a0);    "
"               lw      a3,4(a1);    "
"               and     t0,a2,t3;    "
"               or      t1,a2,t3;    "
"               add     t0,t0,t3;    "
"               or      t0,t0,t1;    "
"               bne     t0,t2,.K4;   "
"               bne     a2,a3,.K3;   "
"               lw      a2,8(a0);    "
"               lw      a3,8(a1);    "
"               and     t0,a2,t3;    "
"               or      t1,a2,t3;    "
"               add     t0,t0,t3;    "
"               or      t0,t0,t1;    "
"               bne     t0,t2,.K5;   "
"               addi    a0,a0,12;    "
"               addi    a1,a1,12;    "
"               beq     a2,a3,.K6;   "
"  .K3:         slli    a4,a2,0x10;  "
"               slli    a5,a3,0x10;  "
"               bne     a4,a5,.K7;   "
"               srli    a4,a2,0x10;  "
"               srli    a5,a3,0x10;  "
"               sub     a0,a4,a5;    "
"               andi    a1,a0,255;   "
"               bnez    a1,.K8;      "
"               ret;                 "
"  .K7:         srli    a4,a4,0x10;  "
"               srli    a5,a5,0x10;  "
"               sub     a0,a4,a5;    "
"               andi    a1,a0,255;   "
"               bnez    a1,.K8;      "
"               ret;                 "
"  .K8:         andi    a4,a4,255;   "
"               andi    a5,a5,255;   "
"               sub     a0,a4,a5;    "
"               ret;                 "
"  .K1:         lbu     a2,0(a0);    "
"               lbu     a3,0(a1);    "
"               addi    a0,a0,1;     "
"               addi    a1,a1,1;     "
"               bne     a2,a3,.K9;   "
"               bnez    a2,.K1;      "
"  .K9:         sub     a0,a2,a3;    "
"               ret;                 "
"  .K4:         addi    a0,a0,4;     "
"               addi    a1,a1,4;     "
"  .K2:         bne     a2,a3,.K1;   "
"               li      a0,0;        "
"               ret;                 "
"  .K5:         addi    a0,a0,8;     "
"               addi    a1,a1,8;     "
"               bne     a2,a3,.K1;   "
"               li      a0,0;        "
"               ret;                 "
);
#endif

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

