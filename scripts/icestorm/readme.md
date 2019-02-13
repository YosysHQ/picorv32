To build the example LED-blinking firmware for an HX8K Breakout Board and get
a timing report (checked against the default 12MHz oscillator):

    $ make clean example.bin timing

To run all the simulation tests:

    $ make clean example_sim synth_sim route_sim FIRMWARE_COUNTER_BITS=4

(You must run the `clean` target to rebuild the firmware with the updated
`FIRMWARE_COUNTER_BITS` parameter; the firmware source must be recompiled for
simulation vs hardware, but this is not tracked as a Makefile dependency.)
