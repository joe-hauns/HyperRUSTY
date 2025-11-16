#!/bin/bash

./run_hltl_1.sh -compare all

./run_hltl_2.sh -compare all

./run_ahltl.sh -compare all

./run_loopcond.sh -all

./run_verilog.sh -all