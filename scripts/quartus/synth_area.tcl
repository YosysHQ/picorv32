read_verilog ../../picorv32.v
read_xdc synth_area.xdc

synth_design -part xc7k70t-fbg676 -top picorv32_axi
opt_design -resynth_seq_area

report_utilization
report_timing
