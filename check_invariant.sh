#!/bin/bash

$APALACHE_HOME/script/run-docker.sh check --init=$2_ --inv=$2 --length=1 --tuning-options='search.invariantFilter=1->.*' $3 $1
