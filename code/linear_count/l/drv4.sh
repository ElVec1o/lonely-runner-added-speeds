#!/bin/bash
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
$D/run2.sh thr2 400 thr2
$D/run2.sh cw 100 cw
$D/run2.sh divsum 400 divsum 100 400 1000 2000 5000
for nr in "134 1" "134 5" "134 33" "267 7" "400 3" "400 60" "1000 2" "1000 333"; do set -- $nr; $D/run2.sh lcov 300 big_$1_$2 big $1 $2 600 11; done
$D/run2.sh lcov 300 pair12_23 pair 12 23 160
$D/run2.sh lcov 300 hunt1_8_44 hunt1 8 44
for n in 134 135 136 137 138 139 140; do $D/run2.sh lcov 300 single_$n single $n 1 $((n/2)) 3 0 20; done
for n in 134 137; do $D/run2.sh lcov 300 splus_$n single $n 1 $((n/2)) 3 1 20; done
$D/run2.sh lcov 400 adv_pilot adv 267 6 2 200000 0 2 0 1
echo ALLDONE >> $D/logs/queue.txt
