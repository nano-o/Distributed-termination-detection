#!/bin/bash

# uses diff to display the latest counterexample to induction found by Apalache
APA_OUTDIR=_apalache-out

TRACE=$(find ${APA_OUTDIR} -type f -name "violation1.tla" -printf "%T@ %p\n" | sort -n | tail -n 1 | cut -d' ' -f2-)

PRE_FILE=$(mktemp)
POST_FILE=$(mktemp)

awk -v RS="" 'NR==4' ${TRACE} | sed '1,2d' >> $PRE_FILE
awk -v RS="" 'NR==5' ${TRACE} | sed '1,2d' >> $POST_FILE
colordiff -y --side-by-side --width=$COLUMNS $PRE_FILE $POST_FILE | less -REX
# or use your favorite editor, e.g.:
# nvim -d $PRE_FILE $POST_FILE
