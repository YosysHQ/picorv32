
# XDC File for Basys3 Board
###########################

set_property PACKAGE_PIN W5 [get_ports clk]
set_property IOSTANDARD LVCMOS33 [get_ports clk]
create_clock -period 10.00 [get_ports clk]

# Pmod Header JA (JA0..JA7)
set_property PACKAGE_PIN J1 [get_ports {out_byte[0]}]
set_property IOSTANDARD LVCMOS33 [get_ports {out_byte[0]}]
set_property PACKAGE_PIN L2 [get_ports {out_byte[1]}]
set_property IOSTANDARD LVCMOS33 [get_ports {out_byte[1]}]
set_property PACKAGE_PIN J2 [get_ports {out_byte[2]}]
set_property IOSTANDARD LVCMOS33 [get_ports {out_byte[2]}]
set_property PACKAGE_PIN G2 [get_ports {out_byte[3]}]
set_property IOSTANDARD LVCMOS33 [get_ports {out_byte[3]}]
set_property PACKAGE_PIN H1 [get_ports {out_byte[4]}]
set_property IOSTANDARD LVCMOS33 [get_ports {out_byte[4]}]
set_property PACKAGE_PIN K2 [get_ports {out_byte[5]}]
set_property IOSTANDARD LVCMOS33 [get_ports {out_byte[5]}]
set_property PACKAGE_PIN H2 [get_ports {out_byte[6]}]
set_property IOSTANDARD LVCMOS33 [get_ports {out_byte[6]}]
set_property PACKAGE_PIN G3 [get_ports {out_byte[7]}]
set_property IOSTANDARD LVCMOS33 [get_ports {out_byte[7]}]

# Pmod Header JB (JB0..JB2)
set_property PACKAGE_PIN A14 [get_ports {resetn}]
set_property IOSTANDARD LVCMOS33 [get_ports {resetn}]
set_property PACKAGE_PIN A16 [get_ports {trap}]
set_property IOSTANDARD LVCMOS33 [get_ports {trap}]
set_property PACKAGE_PIN B15 [get_ports {out_byte_en}]
set_property IOSTANDARD LVCMOS33 [get_ports {out_byte_en}]

