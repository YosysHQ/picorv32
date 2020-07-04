SECTIONS
{
  . = 0x100;
  . = ALIGN(4);
  .text : { *(.text) }
  . = ALIGN(4);
  .data : { *(.data) }
  . = ALIGN(4);
  .bss : { *(.bss) }
  . = ALIGN(4);
}
