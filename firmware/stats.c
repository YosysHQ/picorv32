#include "firmware.h"

static void stats_print_dec(int val, int digits, bool zero_pad)
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
		print_chr(*(--p));
	}
}

void stats()
{
	int num_cycles, num_instr;
	asm("rdcycle %0; rdinstret %1;" : "=r"(num_cycles), "=r"(num_instr));
	print_str("Cycle counter ........");
	stats_print_dec(num_cycles, 8, false);
	print_str("\nInstruction counter ..");
	stats_print_dec(num_instr, 8, false);
	print_str("\nCPI: ");
	stats_print_dec((num_cycles / num_instr), 0, false);
	print_str(".");
	stats_print_dec(((100 * num_cycles) / num_instr) % 100, 2, true);
	print_str("\n");
}

