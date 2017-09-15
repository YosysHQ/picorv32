#include <stdint.h>

#define reg_spictrl (*(volatile uint32_t*)0x02000000)
#define reg_uart_clkdiv (*(volatile uint32_t*)0x02000004)
#define reg_uart_data (*(volatile uint32_t*)0x02000008)
#define reg_leds (*(volatile uint32_t*)0x03000000)

void main()
{
	reg_uart_clkdiv = 104;
	reg_leds = 1;
	reg_uart_data = 'H';
	reg_leds = 2;
	reg_uart_data = 'e';
	reg_leds = 3;
	reg_uart_data = 'l';
	reg_leds = 4;
	reg_uart_data = 'l';
	reg_leds = 5;
	reg_uart_data = 'o';
	reg_leds = 6;
	reg_uart_data = '\r';
	reg_leds = 7;
	reg_uart_data = '\n';
	reg_leds = 8;
}

