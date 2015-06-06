#include <stdint.h>
#include <stdbool.h>
#define OUTPORT 0x10000000

static void print_str(const char *p)
{
	while (*p != 0)
		*((volatile uint32_t*)OUTPORT) = *(p++);
}

static void print_dec(int val, int digits, bool zero_pad)
{
	char buffer[32];
	char *p = buffer;
	while (val || digits > 0) {
		if (val)
			*(p++) = '0' + val % 10;
		else
			*(p++) = zero_pad ? '0' : ' ';
		val = val / 10;
		digits--;
	}
	while (p != buffer) {
		if (p[-1] == ' ' && p[-2] == ' ') p[-1] = '.';
		*((volatile uint32_t*)OUTPORT) = *(--p);
	}
}

void stats()
{
	int num_cycles, num_instr;
	asm("rdcycle %0; rdinstret %1;" : "=r"(num_cycles), "=r"(num_instr));
	print_str("Cycle counter ........");
	print_dec(num_cycles, 8, false);
	print_str("\nInstruction counter ..");
	print_dec(num_instr, 8, false);
	print_str("\nCPI: ");
	print_dec((num_cycles / num_instr), 0, false);
	print_str(".");
	print_dec(((100 * num_cycles) / num_instr) % 100, 2, true);
	print_str("\n");
}

