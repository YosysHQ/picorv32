read_verilog ../../picorv32.v
synth_design -part xc7k70t-fbg676 -top picorv32
report_utilization
