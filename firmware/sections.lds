/*
This is free and unencumbered software released into the public domain.

Anyone is free to copy, modify, publish, use, compile, sell, or
distribute this software, either in source code form or as a compiled
binary, for any purpose, commercial or non-commercial, and by any
means.
*/

MEMORY {
	mem : ORIGIN = 0x00000000, LENGTH = 0x00010000
}

SECTIONS {
	.memory : {
		. = 0x000000;
		start*(.text);
		*(.text);
		*(*);
		end = .;
	} > mem
}
