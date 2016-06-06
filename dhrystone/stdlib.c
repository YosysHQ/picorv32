#include <stdarg.h>

extern long time();
extern long insn();
extern char *malloc();
extern int printf(const char *format, ...);
extern int scanf(const char *format, ...);

// implementations are copy&paste from riscv newlib
extern void *memcpy(void *dest, const void *src, long n);
extern char *strcpy(char *dest, const char *src);
extern int strcmp(const char *s1, const char *s2);

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
		asm("ebreak");
	return p;
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

// -------------------------------------------------------
// Copy&paste from RISC-V newlib:

void* memcpy(void* aa, const void* bb, long n)
{
  #define BODY(a, b, t) { \
    t tt = *b; \
    a++, b++; \
    *(a-1) = tt; \
  }

  char* a = (char*)aa;
  const char* b = (const char*)bb;
  char* end = a+n;
  unsigned long msk = sizeof(long)-1;
  if (__builtin_expect(((unsigned long)a & msk) != ((unsigned long)b & msk) || n < sizeof(long), 0))
  {
small:
    if (__builtin_expect(a < end, 1))
      while (a < end)
        BODY(a, b, char);
    return aa;
  }

  if (__builtin_expect(((unsigned long)a & msk) != 0, 0))
    while ((unsigned long)a & msk)
      BODY(a, b, char);

  long* la = (long*)a;
  const long* lb = (const long*)b;
  long* lend = (long*)((unsigned long)end & ~msk);

  if (__builtin_expect(la < lend-8, 0))
  {
    while (la < lend-8)
    {
      long b0 = *lb++;
      long b1 = *lb++;
      long b2 = *lb++;
      long b3 = *lb++;
      long b4 = *lb++;
      long b5 = *lb++;
      long b6 = *lb++;
      long b7 = *lb++;
      long b8 = *lb++;
      *la++ = b0;
      *la++ = b1;
      *la++ = b2;
      *la++ = b3;
      *la++ = b4;
      *la++ = b5;
      *la++ = b6;
      *la++ = b7;
      *la++ = b8;
    }
  }

  while (la < lend)
    BODY(la, lb, long);

  a = (char*)la;
  b = (const char*)lb;
  if (__builtin_expect(a < end, 0))
    goto small;
  return aa;
}

static inline unsigned long __libc_detect_null(unsigned long w)
{
  unsigned long mask = 0x7f7f7f7f;
  if (sizeof(long) == 8)
    mask = ((mask << 16) << 16) | mask;
  return ~(((w & mask) + mask) | w | mask);
}

char* strcpy(char* dst, const char* src)
{
  char* dst0 = dst;

#if !defined(PREFER_SIZE_OVER_SPEED) && !defined(__OPTIMIZE_SIZE__)
  int misaligned = ((unsigned long)dst | (unsigned long)src) & (sizeof(long)-1);
  if (__builtin_expect(!misaligned, 1))
  {
    long* ldst = (long*)dst;
    const long* lsrc = (const long*)src;

    while (!__libc_detect_null(*lsrc))
      *ldst++ = *lsrc++;

    dst = (char*)ldst;
    src = (const char*)lsrc;

    char c0 = src[0];
    char c1 = src[1];
    char c2 = src[2];
    if (!(*dst++ = c0)) return dst0;
    if (!(*dst++ = c1)) return dst0;
    char c3 = src[3];
    if (!(*dst++ = c2)) return dst0;
    if (sizeof(long) == 4) goto out;
    char c4 = src[4];
    if (!(*dst++ = c3)) return dst0;
    char c5 = src[5];
    if (!(*dst++ = c4)) return dst0;
    char c6 = src[6];
    if (!(*dst++ = c5)) return dst0;
    if (!(*dst++ = c6)) return dst0;

out:
    *dst++ = 0;
    return dst0;
  }
#endif /* not PREFER_SIZE_OVER_SPEED */

  char ch;
  do
  {
    ch = *src;
    src++;
    dst++;
    *(dst-1) = ch;
  } while(ch);

  return dst0;
}

/* copy&paste from disassembled libc */
// strcmp.S: Artisanally coded in California by A. Shell Waterman
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
