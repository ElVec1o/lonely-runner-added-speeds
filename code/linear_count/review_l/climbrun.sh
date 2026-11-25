#!/bin/bash
cd "$(dirname "${BASH_SOURCE[0]}")"
for spec in "134 1" "267 7" "1000 2" "134 33"; do set -- $spec; TAILN=1 ./run.sh climb_$1_$2 climb $1 $2 120 6000 11 | cut -c1-800; done
