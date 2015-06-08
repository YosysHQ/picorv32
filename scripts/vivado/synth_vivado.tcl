
# vivado -nojournal -log synth_vivado.log -mode batch -source synth_vivado.tcl

read_verilog synth_vivado_soc.v
read_verilog ../../picorv32.v
read_xdc synth_vivado.xdc

synth_design -part xc7a15t-csg324 -top picorv32_axi
# synth_design -part xc7a15t-csg324 -top test_soc
opt_design
place_design
route_design

report_utilization
report_timing

write_verilog -force synth_vivado_syn.v

