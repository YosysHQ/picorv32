#!/bin/bash

dashes="----------------------------------------------------------------"
printf '| %-25s | %-10s | %-20s |\n' "Device" "Speedgrade" "Clock Period (Freq.)"
printf '|:%.25s |:%.10s:| %.20s:|\n' $dashes $dashes $dashes

for x in $( grep -H . tab_*/results.txt )
do
	read _ size device grade _ speed < <( echo "$x" | tr _/: ' ' )
	case "$device" in
		xc7a) d="Xilinx Artix-7T" ;;
		xc7k) d="Xilinx Kintex-7T" ;;
		xc7v) d="Xilinx Virtex-7T" ;;
		xcku) d="Xilinx Kintex UltraScale" ;;
		xcvu) d="Xilinx Virtex UltraScale" ;;
		xckup) d="Xilinx Kintex UltraScale+" ;;
		xcvup) d="Xilinx Virtex UltraScale+" ;;
	esac
	speedtxt=$( printf '%s.%s ns (%d MHz)' ${speed%?} ${speed#?} $((10000 / speed)) )
	printf '| %-25s | %-10s | %20s |\n' "$d" "-$grade" "$speedtxt"
done
