#!/bin/bash
# sequential queue (one job at a time), each through launch_lite.sh via run.sh (ceiling 300 MB,
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd $D
./run.sh thr thr >/dev/null 2>&1
./run.sh lem_10_15 lem 10 15 6 >/dev/null 2>&1
./run.sh lem_16_40 lem 16 40 3 >/dev/null 2>&1
for k in 1 2 3 4 5 6; do
  case $k in 1) NS="11 20 96";; 2) NS="15 40 130";; 3) NS="22 60 130";; 4) NS="29 70 130";; 5) NS="36 80 130";; 6) NS="43 90 130";; esac
  for N in $NS; do
    if [ $N -le 60 ]; then WM=$((3*N*N*N)); else WM=$((20*N*N)); fi
    for R in 1 3 $((N/3)) $((N*3/5)); do
      ./run.sh dc_${k}_${N}_${R} dc $k $N $R $WM 2000 25 12345 >/dev/null 2>&1
    done
  done
done
echo done > $D/logs/DRV_DONE
