SECTIONS {
	.memory : {
		sram = 0;
		*(.data);
		*(.bss);
		. = 0x100000;
		start*(.text);
		*(.text);
		*(*);
	}
}
