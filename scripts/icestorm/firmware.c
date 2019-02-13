#include <stdint.h>

#ifndef SHIFT_COUNTER_BITS
#error SHIFT_COUNTER_BITS must be defined as 4 (for simulation) or 18 (for hardware bitstreams)!
#endif

void output(uint8_t c)
{
	*(volatile char*)0x10000000 = c;
}

uint8_t gray_encode_simple(uint8_t c)
{
	return c ^ (c >> 1);
}

uint8_t gray_encode_bitwise(uint8_t c)
{
	unsigned int in_buf = c, out_buf = 0, bit = 1;
	for (int i = 0; i < 8; i++) {
		if ((in_buf & 1) ^ ((in_buf >> 1) & 1))
			out_buf |= bit;
		in_buf = in_buf >> 1;
		bit = bit << 1;
	}
	return out_buf;
}

uint8_t gray_decode(uint8_t c)
{
	uint8_t t = c >> 1;
	while (t) {
		c = c ^ t;
		t = t >> 1;
	}
	return c;
}

void gray(uint8_t c)
{
	uint8_t gray_simple = gray_encode_simple(c);
	uint8_t gray_bitwise = gray_encode_bitwise(c);
	uint8_t gray_decoded = gray_decode(gray_simple);

	if (gray_simple != gray_bitwise || gray_decoded != c)
		while (1) asm volatile ("ebreak");

	output(gray_simple);
}

void main()
{
	for (uint32_t counter = (2+4+32+64) << SHIFT_COUNTER_BITS;; counter++) {
		asm volatile ("" : : "r"(counter));
		if ((counter & ~(~0 << SHIFT_COUNTER_BITS)) == 0)
			gray(counter >> SHIFT_COUNTER_BITS);
	}
}
