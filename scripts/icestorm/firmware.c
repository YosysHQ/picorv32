#include <stdint.h>

// use SHIFT_COUNTER_BITS=4 for simulation
#define SHIFT_COUNTER_BITS 16

void output(uint8_t c)
{
	*(volatile char*)0x10000000 = c;
}

void output_gray(uint8_t c)
{
	unsigned int in_buf = c, out_buf = 0;
	for (int i = 0; i < 8; i++) {
		unsigned int bit = (in_buf & 1) ^ ((in_buf >> 1) & 1);
		in_buf = in_buf >> 1;
		out_buf = (out_buf << 1) | bit;
	}
	output(out_buf);
}

void main()
{
	for (uint32_t counter = (2+4+32+64) << SHIFT_COUNTER_BITS;; counter++) {
		asm volatile ("" : : "r"(counter));
		if ((counter & ~(~0 << SHIFT_COUNTER_BITS)) == 0)
			output_gray(counter >> SHIFT_COUNTER_BITS);
	}
}
