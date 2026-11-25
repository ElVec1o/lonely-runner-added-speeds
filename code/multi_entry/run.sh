#!/bin/bash
# usage: run.sh NAME bin args... -> launch_lite.sh, 300 MB ceiling
NAME=$1; BIN=$2; shift 2
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
rm -f $D/logs/$NAME.out $D/logs/$NAME.err $D/logs/$NAME.watch
bash "${LAUNCH_LITE:?set LAUNCH_LITE to code/tools/launch_lite.sh}" 300 $D/logs $NAME $D/bin/$BIN "$@" >/dev/null 2>&1
echo "== $NAME: $(tail -1 $D/logs/$NAME.watch)"
