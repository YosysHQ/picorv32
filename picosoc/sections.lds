SECTIONS {
	.memory : {
		. = 0x100000;
		start*(.text);
		*(.text);
		*(*);
	}
}
