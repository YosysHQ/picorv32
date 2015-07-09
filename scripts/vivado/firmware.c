void putc(char c)
{
	*(volatile char*)0x10000000 = c;
}

void puts(const char *s)
{
	while (*s) putc(*s++);
}

void main()
{
	puts("Hello World!\n");
}
