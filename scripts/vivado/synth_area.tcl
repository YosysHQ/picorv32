
read_verilog ../../picorv32.v
read_xdc synth_area.xdc

synth_design -part xc7a15t-fgg484 -top picorv32_axi
opt_design
place_design
route_design

report_utilization
report_timing

write_verilog -force synth_area.v

