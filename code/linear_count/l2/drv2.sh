#!/bin/bash
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
L=$D/logs; B=$D/target/release/l2; J="${LAUNCH_LITE:?set LAUNCH_LITE to code/tools/launch_lite.sh}"
run(){ name=$1; shift; echo "START $name $(date +%T)" >> $L/drv.log; bash $J 400 $L $name $B "$@" >/dev/null 2>&1; echo "END $name rc=$? $(date +%T)" >> $L/drv.log; }
run exc1 exc1 8 44
for k in 1 2 3 4 5 6; do
  for N in $((7*k+1)) $((7*k+3)) $((8*k+3)) $((10*k+10)) $((12*k+20)); do
    run dc_k${k}_N${N} dc $k $N all 3 30
  done
done
run neg400 neg 400 2
run negs5000 negs 5000 2
run negs1000 negs 1000 4
run big61_100 big 61 20 1,2,3,6,30,59 2
run big267 big 267 3 1 0
echo "ALL DONE $(date +%T)" >> $L/drv.log
