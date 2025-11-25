#!/bin/bash

group_name="$1"; shift
case_name="$1"; shift
TO_SMT=${TO_SMT:-target/release/to-smt}
echo $*

YOSYS_PATTERN='.*-v((\s+\S+.ys)+\s)-t\s+(\S+)\s+.*-o\s+(\S+)\s+-f(\s+\S+).*'
if echo $* | rg -q '.*-n((\s+\S+)+)\s+-f(\s+\S+).*'
then

  nusmv=$(echo $* | rg '.*-n((\s+\S+)+)\s+-f(\s+\S+).*'  -r '$1')
  form=$( echo $* | rg '.*-n((\s+\S+)+)\s+-f(\s+\S+).*'  -r '$3')
  args="$(for x in $nusmv; do echo " -n $x"; done) -f $form"

elif echo $* | rg -q "$YOSYS_PATTERN"
then

  echo $*
  verilog=$(echo $* | rg "$YOSYS_PATTERN"  -r '$1')
  form=$(   echo $* | rg "$YOSYS_PATTERN"  -r '$5')
  yosys_out=$(   echo $* | rg "$YOSYS_PATTERN"  -r '$4')
  top=$(   echo $* | rg "$YOSYS_PATTERN"  -r '$3')
  echo verilog=$verilog
  args="
    $(for x in $verilog 
    do 
      echo " -v $x"
    done)
    -t $top
    -o $yosys_out
    -f $form
  "

else 

  echo "unexpected HyperRUSTY call: $*"
  exit -1

fi

mkdir -p smt-benchmarks/$group_name
./write-vimspector-files.sh $TO_SMT $args --output-file smt-benchmarks/$group_name/$case_name.smt2
$TO_SMT $args --output-file smt-benchmarks/$group_name/$case_name.smt2

# nusmv=$(echo $* | rg '.*-n((\s+\S+)+)\s+-f.*'  -r '$1')
# form=$(echo $* | rg '.*-n((\s+\S+)+)\s+-f(\s+\S+).*'  -r '$3')
# mkdir -p smt-benchmarks/$group_name
# $TO_SMT $(for x in $nusmv; do printf "%s " "-n $x"; done) -f $form --output-file smt-benchmarks/$group_name/$case_name.smt2
