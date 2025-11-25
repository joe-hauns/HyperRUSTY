#!/bin/bash
cargo=$(which cargo)

RELEASE=1

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


to-smt(){
  ./write-vimspector-files.sh $bin $*
  $bin $*
}

# ./export-smt2.sh other Tictac target/release/HyperRUSTY -n benchmarks/sync/17_tictac/tictac.smv benchmarks/sync/17_tictac/tictac.smv -f benchmarks/sync/17_tictac/determinism.hq -k 20 -s hpes # <-- HyperRUSTY parser crashes
./export-smt2.sh other Infoflow target/release/HyperRUSTY -n benchmarks/sync/0_infoflow/info.smv benchmarks/sync/0_infoflow/info.smv -f benchmarks/sync/0_infoflow/info.hq -k 20 -s hpes
EXPORT_SMT=1 ./run_hltl_1.sh -all smt
EXPORT_SMT=1 ./run_hltl_2.sh -all smt
EXPORT_SMT=1 ./run_loopcond.sh -all smt
EXPORT_SMT=1 ./run_verilog.sh -all smt
# # EXPORT_SMT=1 ./run_ahltl.sh -all smt
