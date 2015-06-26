// A simple Sieve of Eratosthenes

#include <stdint.h>
#include <stdbool.h>

#define BITMAP_SIZE 64
#define OUTPORT 0x10000000

static uint32_t bitmap[BITMAP_SIZE/32];

static void bitmap_set(int idx)
{
	bitmap[idx/32] |= 1 << (idx % 32);
}

static bool bitmap_get(int idx)
{
	return (bitmap[idx/32] & (1 << (idx % 32))) != 0;
}

static void print_chr(char ch)
{
	*((volatile uint32_t*)OUTPORT) = ch;
}

static void print_str(const char *p)
{
	while (*p != 0)
		*((volatile uint32_t*)OUTPORT) = *(p++);
}

static void print_dec(int val)
{
	char buffer[10];
	char *p = buffer;
	while (val || p == buffer) {
		*(p++) = val % 10;
		val = val / 10;
	}
	while (p != buffer) {
		*((volatile uint32_t*)OUTPORT) = '0' + *(--p);
	}
}

static void print_hex(unsigned int val)
{
	int i;
	for (i = 32-4; i >= 0; i -= 4)
		*((volatile uint32_t*)OUTPORT) = "0123456789ABCDEF"[(val >> i) % 16];
}

static void print_prime(int idx, int val)
{
	if (idx < 10)
		print_str(" ");
	print_dec(idx);
	if (idx / 10 == 1)
		goto force_th;
	switch (idx % 10) {
		case 1: print_str("st"); break;
		case 2: print_str("nd"); break;
		case 3: print_str("rd"); break;
	force_th:
		default: print_str("th"); break;
	}
	print_str(" prime is ");
	print_dec(val);
	print_str(".\n");
}

void sieve()
{
	int i, j, k;
	int idx = 1;
	print_prime(idx++, 2);
	for (i = 0; i < BITMAP_SIZE; i++) {
		if (bitmap_get(i))
			continue;
		print_prime(idx++, 3+2*i);
		for (j = 2*(3+2*i);; j += 3+2*i) {
			if (j%2 == 0)
				continue;
			k = (j-3)/2;
			if (k >= BITMAP_SIZE)
				break;
			bitmap_set(k);
		}
	}
}

uint32_t *irq(uint32_t *regs, uint32_t irqs)
{
	static int ext_irq_4_count = 0;
	static int ext_irq_5_count = 0;
	static int timer_irq_count = 0;

	if ((irqs & (1<<4)) != 0) {
		ext_irq_4_count++;
		// print_str("[EXT-IRQ-4]");
	}

	if ((irqs & (1<<5)) != 0) {
		ext_irq_5_count++;
		// print_str("[EXT-IRQ-5]");
	}

	if ((irqs & 1) != 0) {
		timer_irq_count++;
		// print_str("[TIMER-IRQ]");
	}

	if ((irqs & 6) != 0)
	{
		int i, k;
		uint32_t pc = regs[0] - 4;
		uint32_t instr = *(uint32_t*)pc;

		print_str("\n");
		print_str("------------------------------------------------------------\n");

		if ((irqs & 2) != 0) {
			if (instr == 0x00100073) {
				print_str("SBREAK instruction at 0x");
				print_hex(pc);
				print_str("\n");
			} else {
				print_str("Illegal Instruction at 0x");
				print_hex(pc);
				print_str(": 0x");
				print_hex(instr);
				print_str("\n");
			}
		}

		if ((irqs & 4) != 0) {
			print_str("Bus error in Instruction at 0x");
			print_hex(pc);
			print_str(": 0x");
			print_hex(instr);
			print_str("\n");
		}

		for (i = 0; i < 8; i++)
		for (k = 0; k < 4; k++)
		{
			int r = i + k*8;

			if (r == 0) {
				print_str("pc  ");
			} else
			if (r < 10) {
				print_chr('x');
				print_chr('0' + r);
				print_chr(' ');
				print_chr(' ');
			} else
			if (r < 20) {
				print_chr('x');
				print_chr('1');
				print_chr('0' + r - 10);
				print_chr(' ');
			} else
			if (r < 30) {
				print_chr('x');
				print_chr('2');
				print_chr('0' + r - 20);
				print_chr(' ');
			} else {
				print_chr('x');
				print_chr('3');
				print_chr('0' + r - 30);
				print_chr(' ');
			}

			print_hex(regs[r]);
			print_str(k == 3 ? "\n" : "    ");
		}

		print_str("------------------------------------------------------------\n");

		print_str("Number of fast external IRQs counted: ");
		print_dec(ext_irq_4_count);
		print_str("\n");

		print_str("Number of slow external IRQs counted: ");
		print_dec(ext_irq_5_count);
		print_str("\n");

		print_str("Number of timer IRQs counted: ");
		print_dec(timer_irq_count);
		print_str("\n");

		__asm__("sbreak");
	}

	return regs;
}

