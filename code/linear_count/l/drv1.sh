#!/bin/bash
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
$D/run.sh 400 scan16_60 scan 16 60 3 1 > $D/logs/drv1.txt 2>&1
