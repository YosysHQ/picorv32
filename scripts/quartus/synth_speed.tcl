
read_verilog ../../picorv32.v
read_xdc synth_speed.xdc

synth_design -part xc7k70t-fbg676 -top picorv32_axi
opt_design
place_design
phys_opt_design
route_design

report_utilization
report_timing

