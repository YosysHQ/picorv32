SECTIONS {
. = 0x00000000;
.text : { *(.text) }
_ftext = 0x00010000;
}
