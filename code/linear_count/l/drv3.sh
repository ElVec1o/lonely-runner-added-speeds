#!/bin/bash
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
while ! grep -q ALLDONE $D/logs/queue.txt 2>/dev/null; do sleep 10; done
$D/run2.sh thr2 400 thr2
$D/run2.sh cw 100 cw
$D/run2.sh divsum 400 divsum 100 400 1000 2000 5000
$D/run2.sh lcov 400 adv_pilot adv 267 6 2 200000 0 2 0 1
echo PILOTDONE >> $D/logs/queue.txt
