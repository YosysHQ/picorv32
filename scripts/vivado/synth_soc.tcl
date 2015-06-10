
read_verilog soc_top.v
read_verilog ../../picorv32.v
read_xdc synth_soc.xdc

synth_design -part xc7a35t-cpg236-1 -top soc_top
opt_design
place_design
route_design

report_utilization
report_timing

write_verilog -force synth_soc.v
write_bitstream -force synth_soc.bit
# write_mem_info -force synth_soc.mmi

