// This is free and unencumbered software released into the public domain.
//
// Anyone is free to copy, modify, publish, use, compile, sell, or
// distribute this software, either in source code form or as a compiled
// binary, for any purpose, commercial or non-commercial, and by any
// means.

#define q0 0
#define q1 1
#define q2 2
#define q3 3

.macro getq rd qs
custom0 \rd,\qs,0,0
.endm

.macro setq qd rs
custom0 \qd,\rs,0,1
.endm

.macro retirq
custom0 0,0,0,2
.endm

.macro maskirq rd rs
custom0 \rd,\rs,0,3
.endm

.macro waitirq rd
custom0 \rd,0,0,4
.endm

.macro timer rd rs
custom0 \rd,\rs,0,5
.endm

