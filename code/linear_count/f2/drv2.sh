#!/bin/bash
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd $D
./run.sh lem_42 lem 42 42 3 >/dev/null 2>&1
./run.sh lem_134_q20 lem 134 134 -20 >/dev/null 2>&1
./run.sh ctl2 ctl >/dev/null 2>&1
echo done > $D/logs/DRV2_DONE
