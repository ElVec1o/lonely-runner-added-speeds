#!/bin/bash
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
while ! grep -q ALLDONE $D/logs/queue.txt 2>/dev/null; do sleep 15; done
mv $D/bin/lcov_q $D/bin/lcov
$D/run2.sh lcov 300 scanq134 scan 134 135 -3 2
$D/run2.sh lcov 300 scanq250 scan 250 250 -3 11
echo Q8DONE >> $D/logs/queue.txt
