#!/bin/bash
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
while ! grep -q ADVDONE $D/logs/queue.txt 2>/dev/null; do sleep 10; done
mv $D/bin/lcov_a $D/bin/lcov
i=0
for t in "80 1 1" "80 6 1" "100 33 1" "130 1 2" "150 6 2" "180 40 2" "200 1 3" "260 6 3" "400 6 3" "420 1 4" "600 6 5" "830 1 6" "830 12 6"; do i=$((i+1)); set -- $t; $D/run2.sh lcov 300 alive_$i alive $1 $2 $3 40 5; done
echo ALIVEDONE >> $D/logs/queue.txt
