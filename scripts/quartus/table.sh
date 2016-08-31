#!/bin/bash

dashes="----------------------------------------------------------------"
printf '| %-25s | %-10s | %-20s |\n' "Device" "Speedgrade" "Clock Period (Freq.)"
printf '|:%.25s |:%.10s:| %.20s:|\n' $dashes $dashes $dashes

for x in $( grep -H . tab_*/results.txt )
do
	read _ size device grade _ speed < <( echo "$x" | tr _/: ' ' )
	case "$device" in
		ep4ce)  d="Altera Cyclone IV E" ;;
		ep4cgx) d="Altera Cyclone IV GX" ;;
		5cgx)   d="Altera Cyclone V GX" ;;
	esac
	speedtxt=$( printf '%s.%s ns (%d MHz)' ${speed%?} ${speed#?} $((10000 / speed)) )
	printf '| %-25s | %-10s | %20s |\n' "$d" "-$grade" "$speedtxt"
done
