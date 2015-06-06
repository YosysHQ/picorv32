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

static void print_str(const char *p)
{
	while (*p != 0)
		*((volatile uint32_t*)OUTPORT) = *(p++);
}

static void print_dec(int val)
{
	char buffer[10];
	char *p = buffer;
	while (val) {
		*(p++) = val % 10;
		val = val / 10;
	}
	while (p != buffer) {
		*((volatile uint32_t*)OUTPORT) = '0' + *(--p);
	}
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

