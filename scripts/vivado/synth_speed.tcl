
read_verilog ../../picorv32.v
read_xdc synth_speed.xdc

synth_design -part xc7a15t-csg324 -top picorv32_axi
opt_design
place_design
route_design

report_utilization
report_timing

write_verilog -force synth_speed.v

