#!/bin/bash

for i in Inv1 Inv2 Inv3 Inv4 Correctness; do
        $APALACHE_HOME/script/run-docker.sh check --init=${i}_ --inv=${i} --length=1 --no-deadlock --discard-disabled=false --tuning-options='search.invariantFilter=1->.*' Termination.tla || exit 1
done
