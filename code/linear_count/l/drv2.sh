#!/bin/bash
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
while ps aux | grep -q "[b]in/lcov scan"; do sleep 5; done
mv $D/bin/lcov_new $D/bin/lcov
$D/run2.sh lcov 300 ctl2 ctl
$D/run2.sh thr 400 thr
$D/run2.sh lcov 300 xcheck2 xcheck 3000 4000
$D/run2.sh lcov 400 scanp16_40 scanp 16 40 3 1 6
for nr in "134 1" "134 5" "134 33" "267 7" "267 30" "400 3" "400 60" "400 199" "1000 2" "1000 333" "2000 11"; do set -- $nr; $D/run2.sh lcov 300 big_$1_$2 big $1 $2 4000 11; done
$D/run2.sh lcov 300 pair13_23 pair 12 23 160
$D/run2.sh lcov 300 hunt1_8_44 hunt1 8 44
for n in 134 135 136 137 138 139 140; do $D/run2.sh lcov 300 single_$n single $n 1 $((n/2)) 3 0 20; done
for n in 134 137; do $D/run2.sh lcov 300 splus_$n single $n 1 $((n/2)) 3 1 20; done
echo ALLDONE >> $D/logs/queue.txt
