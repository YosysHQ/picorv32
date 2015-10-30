#!/bin/bash

set -ex

rm -rf synplify.tmp
mkdir synplify.tmp
cd synplify.tmp

cat > impl_syn.prj << EOT
add_file -verilog -lib work ../../../picorv32.v
impl -add impl -type fpga

# implementation attributes
set_option -vlog_std v2001
set_option -project_relative_includes 1

# device options
set_option -technology SBTiCE40
set_option -part iCE40HX8K
set_option -package CT256
set_option -speed_grade
set_option -part_companion ""

# compilation/mapping options
set_option -top_module "picorv32"

# mapper_options
set_option -frequency auto
set_option -write_verilog 0
set_option -write_vhdl 0

# Silicon Blue iCE40
set_option -maxfan 10000
set_option -disable_io_insertion 0
set_option -pipe 1
set_option -retiming 0
set_option -update_models_cp 0
set_option -fixgatedclocks 2
set_option -fixgeneratedclocks 0

# NFilter
set_option -popfeed 0
set_option -constprop 0
set_option -createhierarchy 0

# sequential_optimization_options
set_option -symbolic_fsm_compiler 1

# Compiler Options
set_option -compiler_compatible 0
set_option -resource_sharing 1

# automatic place and route (vendor) options
set_option -write_apr_constraint 1

# set result format/file last
project -result_format edif
project -result_file impl.edf
impl -active impl
project -run synthesis -clean
EOT

icecubedir="${ICECUBEDIR:-/opt/lscc/iCEcube2.2014.08}"
export SBT_DIR="$icecubedir/sbt_backend"
export SYNPLIFY_PATH="$icecubedir/synpbase"
export LM_LICENSE_FILE="$icecubedir/license.dat"
export TCL_LIBRARY="$icecubedir/sbt_backend/bin/linux/lib/tcl8.4"
export LD_LIBRARY_PATH="$LD_LIBRARY_PATH${LD_LIBRARY_PATH:+:}$icecubedir/sbt_backend/bin/linux/opt"
export LD_LIBRARY_PATH="$LD_LIBRARY_PATH${LD_LIBRARY_PATH:+:}$icecubedir/sbt_backend/bin/linux/opt/synpwrap"
export LD_LIBRARY_PATH="$LD_LIBRARY_PATH${LD_LIBRARY_PATH:+:}$icecubedir/sbt_backend/lib/linux/opt"
export LD_LIBRARY_PATH="$LD_LIBRARY_PATH${LD_LIBRARY_PATH:+:}$icecubedir/LSE/bin/lin"
"$icecubedir"/sbt_backend/bin/linux/opt/synpwrap/synpwrap -prj impl_syn.prj -log impl.srr

grep 'instance.*cellRef' impl/impl.edf | sed 's,.*cellRef *,,; s,[ )].*,,;' | sort | uniq -c
