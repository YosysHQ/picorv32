#!/bin/bash

set -e
read _ ip dev grade _ < <( echo $* | tr '_/' ' '; )

# rm -rf tab_${ip}_${dev}_${grade}
mkdir -p tab_${ip}_${dev}_${grade}
cd tab_${ip}_${dev}_${grade}

best_speed=99
speed=20
step=16

synth_case() {
	if [ -f test_${1}.txt ]; then
		echo "Reusing cached tab_${ip}_${dev}_${grade}/test_${1}."
		return
	fi

	case "${dev}" in
		xc7k) xl_device="xc7k70t-fbg676-${grade}" ;;
		xc7v) xl_device="xc7v585t-ffg1761-${grade}" ;;
		xcku) xl_device="xcku035-fbva676-${grade}-e" ;;
		xcvu) xl_device="xcvu065-ffvc1517-${grade}-e" ;;
		xckup) xl_device="xcku3p-ffva676-${grade}-e" ;;
		xcvup) xl_device="xcvu3p-ffvc1517-${grade}-e" ;;
	esac

	cat > test_${1}.tcl <<- EOT
		read_verilog ../tabtest.v
		read_verilog ../../../picorv32.v
		read_xdc test_${1}.xdc
		synth_design -flatten_hierarchy full -part ${xl_device} -top top
		opt_design -sweep -remap -propconst
		opt_design -directive Explore
		place_design -directive Explore
		phys_opt_design -retime -rewire -critical_pin_opt -placement_opt -critical_cell_opt
		route_design -directive Explore
		place_design -post_place_opt
		phys_opt_design -retime
		route_design -directive NoTimingRelaxation
		report_utilization
		report_timing
	EOT

	cat > test_${1}.xdc <<- EOT
		create_clock -period ${speed%?}.${speed#?} [get_ports clk]
	EOT

	echo "Running tab_${ip}_${dev}_${grade}/test_${1}.."
	if ! $VIVADO -nojournal -log test_${1}.log -mode batch -source test_${1}.tcl > /dev/null 2>&1; then
		cat test_${1}.log
		exit 1
	fi
	mv test_${1}.log test_${1}.txt
}

got_violated=false
got_met=false

countdown=2
while [ $countdown -gt 0 ]; do
	synth_case $speed

	if grep -q '^Slack.*(VIOLATED)' test_${speed}.txt; then
		echo "        tab_${ip}_${dev}_${grade}/test_${speed} VIOLATED"
		step=$((step / 2))
		speed=$((speed + step))
		got_violated=true
	elif grep -q '^Slack.*(MET)' test_${speed}.txt; then
		echo "        tab_${ip}_${dev}_${grade}/test_${speed} MET"
		[ $speed -lt $best_speed ] && best_speed=$speed
		step=$((step / 2))
		speed=$((speed - step))
		got_met=true
	else
		echo "ERROR: No slack line found in $PWD/test_${speed}.txt!"
		exit 1
	fi

	if [ $step -eq 0 ]; then
		countdown=$((countdown - 1))
		speed=$((best_speed - 2))
		step=1
	fi
done

if ! $got_violated; then
	echo "ERROR: No timing violated in $PWD!"
	exit 1
fi

if ! $got_met; then
	echo "ERROR: No timing met in $PWD!"
	exit 1
fi


echo "-----------------------"
echo "Best speed for tab_${ip}_${dev}_${grade}: $best_speed"
echo "-----------------------"
echo $best_speed > results.txt

