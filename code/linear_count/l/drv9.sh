#!/bin/bash
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
while ! grep -q Q8DONE $D/logs/queue.txt 2>/dev/null; do sleep 15; done
$D/run2.sh thr4 500 thr4
echo T4DONE >> $D/logs/queue.txt
