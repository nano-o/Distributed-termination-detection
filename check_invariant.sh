#!/bin/bash

$APALACHE_HOME/script/run-docker.sh check --init=$1_ --inv=$1 --length=1 --tuning-options='search.invariantFilter=1->.*' $2
