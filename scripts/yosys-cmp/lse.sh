#!/bin/bash

set -ex

rm -rf lse.tmp
mkdir lse.tmp
cd lse.tmp

cat > lse.prj << EOT
#device
-a SBTiCE40
-d iCE40HX8K
-t CT256
#constraint file

#options
-frequency 200
-optimization_goal Area
-twr_paths 3
-bram_utilization 100.00
-ramstyle Auto
-romstyle Auto
-use_carry_chain 1
-carry_chain_length 0
-resource_sharing 1
-propagate_constants 1
-remove_duplicate_regs 1
-max_fanout 10000
-fsm_encoding_style Auto
-use_io_insertion 1
-use_io_reg auto
-ifd
-resolve_mixed_drivers 0
-RWCheckOnRam 0
-fix_gated_clocks 1
-top picorv32

-ver "../../../picorv32.v"
-p "."

#set result format/file last
-output_edif output.edf

#set log file
-logfile "lse.log"
EOT

icecubedir="${ICECUBEDIR:-/opt/lscc/iCEcube2.2014.08}"
export FOUNDRY="$icecubedir/LSE"
export LD_LIBRARY_PATH="$LD_LIBRARY_PATH${LD_LIBRARY_PATH:+:}$icecubedir/LSE/bin/lin"
"$icecubedir"/LSE/bin/lin/synthesis -f lse.prj

grep 'viewRef.*cellRef' output.edf | sed 's,.*cellRef *,,; s,[ )].*,,;' | sort | uniq -c
