#!/bin/bash
cargo=$(which cargo)

RELEASE=0

cargo() {
  # $cargo with "./write-vimspector-files.sh" $*
  $cargo $*
  # cat .last_bin
  # cat .last_args
}
if [[ $RELEASE == 1 ]]
then
  cargo build  --release || { exit -1; }
  bin=target/release/to-smt
else
  cargo build  || { exit -1; }
  bin=target/debug/to-smt
fi


export TO_SMT=$bin

EXPORT_SMT=1 ./run_verilog.sh -all smt
EXPORT_SMT=1 ./run_hltl_1.sh -all smt
EXPORT_SMT=1 ./run_hltl_2.sh -all smt
EXPORT_SMT=1 ./run_loopcond.sh -all smt
# EXPORT_SMT=1 ./run_ahltl.sh -all smt

