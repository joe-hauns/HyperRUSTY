#!/bin/bash

# echo $*
bin=$1
args=${@:2}
# echo args: $args
printf '%s' $bin > .last_bin
printf '%s' "$args" > .last_args
