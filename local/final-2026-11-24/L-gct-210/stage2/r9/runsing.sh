#!/bin/bash
# usage: runsing.sh SCRIPT TIMEOUT_SEC  -> SCRIPT.log
ulimit -v 2500000
f=$1; t=$2
echo "START $(date -u +%H:%M:%S) $f" > $f.log
( /usr/bin/time -v timeout $t Singular -q $f ) >> $f.log 2>&1
echo "END $(date -u +%H:%M:%S) exit=$?" >> $f.log
