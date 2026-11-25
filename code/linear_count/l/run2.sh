#!/bin/bash
# usage: run2.sh BIN CEIL NAME args... (BIN = lcov or thr) -> launch_lite.sh,
BIN=$1; CEIL=$2; NAME=$3; shift 3
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
bash "${LAUNCH_LITE:?set LAUNCH_LITE to code/tools/launch_lite.sh}" $CEIL $D/logs $NAME $D/bin/$BIN "$@" >/dev/null 2>&1
echo "== $NAME: $(tail -1 $D/logs/$NAME.watch)" >> $D/logs/queue.txt
