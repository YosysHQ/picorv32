// This is free and unencumbered software released into the public domain.
//
// Anyone is free to copy, modify, publish, use, compile, sell, or
// distribute this software, either in source code form or as a compiled
// binary, for any purpose, commercial or non-commercial, and by any
// means.

#include "firmware.h"

uint32_t *irq(uint32_t *regs, uint32_t irqs)
{
	static unsigned int ext_irq_4_count = 0;
	static unsigned int ext_irq_5_count = 0;
	static unsigned int timer_irq_count = 0;

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

