#!/bin/bash
# usage: runall.sh DIR -> stale-safe verdicts on stdout (see runlog.sh)
L=$(mktemp); $(dirname $0)/runlog.sh $1 300 $L; grep -v DONE $L; rm -f $L
