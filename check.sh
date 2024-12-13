#!/bin/bash

# Script to invoke Apalache
# Also see the file .apalache.cfg for common apalache options

set -ex

MEM=5G

case "$1" in
    -typecheck)
        shift
        FILE="Apa${1}.tla"
        $APA/bin/apalache-mc typecheck $FILE
        ;;
    -inductive)
        shift
        FILE="Apa${2}.tla"
        $APA/bin/apalache-mc check --init=Init --inv=$1 --length=0 $FILE
        JVM_ARGS="-Xmx${MEM}" $APA/bin/apalache-mc check --tuning-options=search.invariant.mode=after:"search.invariantFilter=1->.*:smt.randomSeed=${RANDOM}" --init=$1 --inv=$1 --length=1 $FILE
        ;;
    -implication)
        shift
        FILE="Apa${3}.tla"
        JVM_ARGS="-Xmx${MEM}" $APA/bin/apalache-mc check --tuning-options=search.invariant.mode=after --init=$1 --inv=$2 --length=0 $FILE
        ;;
    -relative)
        shift
        FILE="Apa${3}.tla"
        JVM_ARGS="-Xmx${MEM}" $APA/bin/apalache-mc check --init=Init --inv=$2 --length=0 $FILE
        JVM_ARGS="-Xmx${MEM}" $APA/bin/apalache-mc check --tuning-options=search.invariant.mode=after:"search.invariantFilter=1->.*:smt.randomSeed=${RANDOM}" --init=$1 --inv=$2 --length=1 $FILE
        ;;
esac
