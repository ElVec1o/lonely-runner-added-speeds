#!/bin/bash
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
L=$D/logs; B=$D/target/release/l2; J="${LAUNCH_LITE:?set LAUNCH_LITE to code/tools/launch_lite.sh}"
run(){ name=$1; shift; echo "START $name $(date +%T)" >> $L/drv.log; bash $J 500 $L $name $B "$@" >/dev/null 2>&1; echo "END $name rc=$? $(date +%T)" >> $L/drv.log; }
export L2_THREADS=2
run exc1b exc1 34 44
for k in 4 5 6; do
  for N in $((7*k+1)) $((7*k+3)) $((8*k+3)) $((10*k+10)) $((12*k+20)); do
    run dc_k${k}_N${N} dc $k $N all 3 30
  done
done
for k in 1 2 3 4; do for x in 1 2; do
  [ $x -le $k ] || continue
  for N in $((8*k+3)) $((10*k+10)); do
    export L2_FORCE_OSC=$x
    run dcx_k${k}_x${x}_N${N} dc $k $N all 3 30
    unset L2_FORCE_OSC
  done
done; done
run big267 big 267 3 1 0
echo "ALL DONE $(date +%T)" >> $L/drv.log
