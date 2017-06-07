#!/bin/bash

set -e
read _ ip dev grade _ < <( echo $* | tr '_/' ' '; )

# rm -rf tab_${ip}_${dev}_${grade}
mkdir -p tab_${ip}_${dev}_${grade}
cd tab_${ip}_${dev}_${grade}

max_speed=99
min_speed=01
best_speed=99

synth_case() {
	if [ -f test_${1}.txt ]; then
		echo "Reusing cached tab_${ip}_${dev}_${grade}/test_${1}."
		return
	fi

	case "${dev}" in
		ep4ce)  al_device="ep4ce30f23${grade}" ;;
		ep4cgx) al_device="ep4cgx50df27${grade}" ;;
		5cgx)   al_device="5cgxbc9c6f23${grade}" ;;
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

    if ! $QUARTUS_BIN/quartus_map test_${1}; then
        exit 1
    fi
    if ! $QUARTUS_BIN/quartus_fit --read_settings_files=off --write_settings_files=off test_${1} -c test_${1}; then
        exit 1
    fi
    if ! $QUARTUS_BIN/quartus_sta test_${1} -c test_${1}; then
        exit 1
    fi

	cp output_files/test_${1}.sta.summary test_${1}.txt
}

countdown=7
while [ $countdown -gt 0 ]; do
    speed=$(((max_speed+min_speed)/2))
	synth_case $speed

    if grep -q '^Slack : -' test_${speed}.txt; then
		echo "        tab_${ip}_${dev}_${grade}/test_${speed} VIOLATED"
        min_speed=$((speed))
    elif grep -q '^Slack : [^-]' test_${speed}.txt; then
		echo "        tab_${ip}_${dev}_${grade}/test_${speed} MET"
		[ $speed -lt $best_speed ] && best_speed=$speed
        max_speed=$((speed))
	else
		echo "ERROR: No slack line found in $PWD/test_${speed}.txt!"
		exit 1
	fi

    countdown=$((countdown-1))
done

echo "-----------------------"
echo "Best speed for tab_${ip}_${dev}_${grade}: $best_speed"
echo "-----------------------"
echo $best_speed > results.txt

