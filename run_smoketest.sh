#!/bin/bash

./run_hltl_1.sh -compare light

./run_hltl_2.sh -compare light

./run_ahltl.sh -compare light

./run_loopcond.sh -all

./run_verilog.sh -all