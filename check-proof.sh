#!/bin/bash

# First we check that the invariants hold initially:
for i in Inv1 Inv2 Inv3 Inv4; do
        $APALACHE_HOME/script/run-docker.sh check --init=Init --inv=${i} --length=0 --no-deadlock Termination.tla || exit 1
done
# Then we check that those invariants are inductive:
for i in Inv1 Inv2 Inv3 Inv4; do
        $APALACHE_HOME/script/run-docker.sh check --init=${i}_ --inv=${i} --length=1 --no-deadlock --discard-disabled=false --tuning-options='search.invariantFilter=1->.*' Termination.tla || exit 1
done
# Then we check that the invariant imply the safety property:
$APALACHE_HOME/script/run-docker.sh check --init=Safety_precondition --inv=Safety --length=0 --no-deadlock Termination.tla
