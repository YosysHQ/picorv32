/*
This is free and unencumbered software released into the public domain.

Anyone is free to copy, modify, publish, use, compile, sell, or
distribute this software, either in source code form or as a compiled
binary, for any purpose, commercial or non-commercial, and by any
means.
*/

/* starting address needs to be > 0 due to known bug in RISCV/GNU linker */
MEMORY {
	rom(rwx) : ORIGIN = 0x00000100, LENGTH = 63k
        ram(rwx) : ORIGIN = 0x00020000, LENGTH = 16k
}

ENTRY(_pvstart);

SECTIONS {
	.rom : {
                _pvstart*(.text);
		start*(.text);
                . = 0x100;
                . = ALIGN(4);
		*(.text);
        } > rom

        .data : {
          _data_lma = LOADADDR(.data);
          _data = .;
          __global_pointer$ = . ;
          *(.data .data.* )
          *(.sdata .sdata.*)
           . = ALIGN(4);
          _edata = .;
        } >ram AT>rom

        .bss : {
          _bss_start = .;
          *(.bss .bss.*)
           . = ALIGN(4);
          _bss_end = .;
          _end = .;
        } >ram

}
