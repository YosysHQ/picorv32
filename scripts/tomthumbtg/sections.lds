SECTIONS {
	.memory : {
		. = 0;
		*(.text);
		*(*);
	}
}
