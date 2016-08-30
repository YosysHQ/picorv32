
read_verilog system.v
read_verilog ../../picorv32.v
read_xdc synth_system.xdc

synth_design -part xc7a35t-cpg236-1 -top system
opt_design
place_design
route_design

report_utilization
report_timing

write_verilog -force synth_system.v
write_bitstream -force synth_system.bit
# write_mem_info -force synth_system.mmi

