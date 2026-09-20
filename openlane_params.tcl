# These values are taken from the designs examples in the Openlane repository
set ::env(CLOCK_PORT) "clk"
set ::env(CLOCK_NET) $::env(CLOCK_PORT)
set ::env(GLB_RT_ADJUSTMENT) 0.1
set ::env(SYNTH_MAX_FANOUT) 6
set ::env(CLOCK_PERIOD) "24.73"
set ::env(FP_CORE_UTIL) 30
set ::env(PL_TARGET_DENSITY) [ expr ($::env(FP_CORE_UTIL)+5) / 100.0 ]