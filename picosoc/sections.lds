SECTIONS {
	.memory : {
		sram = 0;
		. = 0x100000;
		start*(.text);
		*(.text);
		*(*);
	}
}
