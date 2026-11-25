#!/bin/bash
# usage: [BIN=name] [CEIL=MB] run.sh NAME args... -> launch_lite.sh
NAME=$1; shift
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CEIL=${CEIL:-400}; B=${BIN:-w2}
bash "${LAUNCH_LITE:?set LAUNCH_LITE to code/tools/launch_lite.sh}" $CEIL $D/logs $NAME $D/bin/$B "$@" >/dev/null 2>&1
echo "== $NAME: $(tail -2 $D/logs/$NAME.watch | tr '\n' ' ')"; cut -c1-300 $D/logs/$NAME.out | head -${LINES_OUT:-60}
