#!/bin/bash
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# instrument controls: the adversary must find the known exceptions
$D/run2.sh lcov 300 advctl_20_6 adv 20 6 2 200 0 3 0 1
$D/run2.sh lcov 300 advctl_29_12 adv 29 12 3 120 0 4 0 1
$D/run2.sh lcov 300 advctl_13_6 adv 13 6 1 120 0 2 0 1
# k = 2, N just above 133*2 = 266 (and above the exact k=2 threshold 222 of Theorem S: new ground is k=3)
for nr in "267 1" "267 6" "267 30" "270 6" "270 133" "272 2" "272 66"; do set -- $nr; $D/run2.sh lcov 400 adv2_$1_$2 adv $1 $2 2 500000 0 3 0 1; done
# k = 3, N just above 133*3 = 399 and below Theorem S's proven 517
for nr in "400 6" "400 60" "400 200" "404 12" "404 101"; do set -- $nr; $D/run2.sh lcov 400 adv3_$1_$2 adv $1 $2 3 400000 0 3 0 1; done
# CRT-structured pools (lifts of 2-3 window moduli with offsets), larger speeds up to 3e7
for nr in "267 6" "267 30" "400 6" "400 60"; do set -- $nr; k=2; [ $1 = 400 ] && k=3; $D/run2.sh lcov 400 advc_$1_$2 adv $1 $2 $k 30000000 400000 3 1 7; done
echo ADVDONE >> $D/logs/queue.txt
