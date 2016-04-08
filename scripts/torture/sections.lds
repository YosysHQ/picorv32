SECTIONS {
	.memory : {
		. = 0x000000;
		*(.text);
		*(*);
		end = .;
	}
}

