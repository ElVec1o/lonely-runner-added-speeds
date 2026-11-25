#!/bin/bash
# sequential adversary jobs, one at a time (each through launch_lite.sh)
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
for spec in "$@"; do set -- $spec; N=$1; r=$2; k=$3; M=$4
  NAME=adv_${N}_${r}_k${k}
  bash "${LAUNCH_LITE:?set LAUNCH_LITE to code/tools/launch_lite.sh}" 400 $D/logs $NAME $D/bin/lrev2 adv $N $r $k $M >/dev/null 2>&1
  echo "== $NAME: $(tail -1 $D/logs/$NAME.watch)"; cat $D/logs/$NAME.out
done
