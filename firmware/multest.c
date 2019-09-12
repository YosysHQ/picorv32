// This is free and unencumbered software released into the public domain.
//
// Anyone is free to copy, modify, publish, use, compile, sell, or
// distribute this software, either in source code form or as a compiled
// binary, for any purpose, commercial or non-commercial, and by any
// means.

#include "firmware.h"

static uint32_t xorshift32(void) {
	static uint32_t x = 314159265;
	x ^= x << 13;
	x ^= x >> 17;
	x ^= x << 5;
	return x;
}

void multest(void)
{
	for (int i = 0; i < 15; i++)
	{
		uint32_t a = xorshift32();
		uint32_t b = xorshift32();

		switch (i)
		{
		case 0:
			a = 0x80000000;
			b = 0xFFFFFFFF;
			break;
		case 1:
			a = 0;
			b = 0;
			break;
		case 2:
			a |= 0x80000000;
			b = 0;
			break;
		case 3:
			a &= 0x7FFFFFFF;
			b = 0;
			break;
		}

		uint64_t au = a, bu = b;
		int64_t as = (int32_t)a, bs = (int32_t)b;

		print_str("input     [");
		print_hex(as >> 32, 8);
		print_str("] ");
		print_hex(a, 8);
		print_str(" [");
		print_hex(bs >> 32, 8);
		print_str("] ");
		print_hex(b, 8);
		print_chr('\n');

		uint32_t h_mul, h_mulh, h_mulhsu, h_mulhu;
		print_str("hard mul   ");

		h_mul = hard_mul(a, b);
		print_hex(h_mul, 8);
		print_str("  ");

		h_mulh = hard_mulh(a, b);
		print_hex(h_mulh, 8);
		print_str("  ");

		h_mulhsu = hard_mulhsu(a, b);
		print_hex(h_mulhsu, 8);
		print_str("  ");

		h_mulhu = hard_mulhu(a, b);
		print_hex(h_mulhu, 8);
		print_chr('\n');

		uint32_t s_mul, s_mulh, s_mulhsu, s_mulhu;
		print_str("soft mul   ");

		s_mul = a * b;
		print_hex(s_mul, 8);
		print_str("  ");

		s_mulh = (as * bs) >> 32;
		print_hex(s_mulh, 8);
		print_str("  ");

		s_mulhsu = (as * bu) >> 32;
		print_hex(s_mulhsu, 8);
		print_str("  ");

		s_mulhu = (au * bu) >> 32;
		print_hex(s_mulhu, 8);
		print_str("  ");

		if (s_mul != h_mul || s_mulh != h_mulh || s_mulhsu != h_mulhsu || s_mulhu != h_mulhu) {
			print_str("ERROR!\n");
			__asm__ volatile ("ebreak");
			return;
		}

		print_str(" OK\n");

		uint32_t h_div, h_divu, h_rem, h_remu;
		print_str("hard div   ");

		h_div = hard_div(a, b);
		print_hex(h_div, 8);
		print_str("  ");

		h_divu = hard_divu(a, b);
		print_hex(h_divu, 8);
		print_str("  ");

		h_rem = hard_rem(a, b);
		print_hex(h_rem, 8);
		print_str("  ");

		h_remu = hard_remu(a, b);
		print_hex(h_remu, 8);
		print_chr('\n');

		uint32_t s_div, s_divu, s_rem, s_remu;
		print_str("soft div   ");

		s_div = b ? as / bs : 0xffffffff;
		print_hex(s_div, 8);
		print_str("  ");

		s_divu = b ? au / bu : 0xffffffff;
		print_hex(s_divu, 8);
		print_str("  ");

		s_rem = b ? as % bs : a;
		print_hex(s_rem, 8);
		print_str("  ");

		s_remu = b ? au % bu : a;
		print_hex(s_remu, 8);
		print_str("  ");

		if (s_div != h_div || s_divu != h_divu || s_rem != h_rem || s_remu != h_remu) {
			print_str("ERROR!\n");
			__asm__ volatile ("ebreak");
			return;
		}

		print_str(" OK\n");
	}
}

