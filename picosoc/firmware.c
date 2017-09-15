#include <stdint.h>

#define reg_spictrl (*(volatile uint32_t*)0x02000000)
#define reg_uart_clkdiv (*(volatile uint32_t*)0x02000004)
#define reg_uart_data (*(volatile uint32_t*)0x02000008)
#define reg_leds (*(volatile uint32_t*)0x03000000)

void print(const char *p)
{
	while (*p) {
		if (*p == '\n')
			reg_uart_data = '\r';
		reg_uart_data = *(p++);
	}
}

char getchar_prompt(char *prompt)
{
	int32_t c = -1;

	uint32_t cycles_begin, cycles_now, cycles;
	__asm__ volatile ("rdcycle %0" : "=r"(cycles_begin));

	if (prompt)
		print(prompt);

	reg_leds = ~0;
	while (c == -1) {
		__asm__ volatile ("rdcycle %0" : "=r"(cycles_now));
		cycles = cycles_now - cycles_begin;
		if (cycles > 12000000) {
			if (prompt)
				print(prompt);
			cycles_begin = cycles_now;
			reg_leds = ~reg_leds;
		}
		c = reg_uart_data;
	}
	reg_leds = 0;
	return c;
}

char getchar()
{
	return getchar_prompt(0);
}

// --------------------------------------------------------

extern uint32_t cmd_read_spi_flash_id_worker_begin;
extern uint32_t cmd_read_spi_flash_id_worker_end;

void cmd_read_spi_flash_id()
{
	uint32_t *src_ptr = &cmd_read_spi_flash_id_worker_begin;
	uint32_t *dst_ptr = (uint32_t*)0;

	while (src_ptr != &cmd_read_spi_flash_id_worker_end)
		*(dst_ptr++) = *(src_ptr++);

	((void(*)())0)();
}

// --------------------------------------------------------

void main()
{
	reg_uart_clkdiv = 104;
	while (getchar_prompt("Press ENTER to continue..\n") != '\r') { /* wait */ }

	print("\n");
	print("  ____  _          ____         ____\n");
	print(" |  _ \\(_) ___ ___/ ___|  ___  / ___|\n");
	print(" | |_) | |/ __/ _ \\___ \\ / _ \\| |\n");
	print(" |  __/| | (_| (_) |__) | (_) | |___\n");
	print(" |_|   |_|\\___\\___/____/ \\___/ \\____|\n");

	while (1)
	{
		print("\n");
		print("\n");
		print("Select an action:\n");
		print("\n");
		print("   [1] Read SPI Flash ID\n");
		print("\n");

		for (int rep = 10; rep > 0; rep--)
		{
			print("Command> ");
			char cmd = getchar();
			if (cmd > 32 && cmd < 127)
				reg_uart_data = cmd;
			print("\n");

			switch (cmd)
			{
			case '1':
				cmd_read_spi_flash_id();
				rep = 0;
				break;
			}
		}
	}
}

