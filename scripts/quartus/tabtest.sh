#!/bin/bash

set -e
read _ ip dev grade _ < <( echo $* | tr '_/' ' '; )

# rm -rf tab_${ip}_${dev}_${grade}
mkdir -p tab_${ip}_${dev}_${grade}
cd tab_${ip}_${dev}_${grade}

best_speed=99
speed=30
step=16

synth_case() {
	if [ -f test_${1}.txt ]; then
		echo "Reusing cached tab_${ip}_${dev}_${grade}/test_${1}."
		return
	fi

	case "${dev}" in
		ep4ce) al_device="ep4ce30f23${grade}" ;;
	esac

	cat > test_${1}.qsf <<- EOT
set_global_assignment -name DEVICE ${al_device}
set_global_assignment -name PROJECT_OUTPUT_DIRECTORY output_files
set_global_assignment -name TOP_LEVEL_ENTITY top
set_global_assignment -name VERILOG_FILE ../tabtest.v
set_global_assignment -name VERILOG_FILE ../../../picorv32.v
set_global_assignment -name SDC_FILE test_${1}.sdc
	EOT

	cat > test_${1}.sdc <<- EOT
		create_clock -period ${speed%?}.${speed#?} [get_ports clk]
	EOT

	echo "Running tab_${ip}_${dev}_${grade}/test_${1}.."
     
    quartus_map test_${1}
    quartus_fit --read_settings_files=off --write_settings_files=off test_${1} -c test_${1}
        
#	if ! $VIVADO -nojournal -log test_${1}.log -mode batch -source test_${1}.tcl > /dev/null 2>&1; then
#		cat test_${1}.log
#		exit 1
#	fi
#	mv test_${1}.log test_${1}.txt
}

countdown=2
while [ $countdown -gt 0 ]; do
	synth_case $speed

	if grep -q '^Slack.*(VIOLATED)' test_${speed}.txt; then
		echo "        tab_${ip}_${dev}_${grade}/test_${speed} VIOLATED"
		[ $speed -eq 38 ] || step=$((step / 2))
		speed=$((speed + step))
	elif grep -q '^Slack.*(MET)' test_${speed}.txt; then
		echo "        tab_${ip}_${dev}_${grade}/test_${speed} MET"
		[ $speed -lt $best_speed ] && best_speed=$speed
		step=$((step / 2))
		speed=$((speed - step))
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

echo "-----------------------"
echo "Best speed for tab_${ip}_${dev}_${grade}: $best_speed"
echo "-----------------------"
echo $best_speed > results.txt

