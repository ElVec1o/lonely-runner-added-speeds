#!/bin/bash
# usage: run2.sh NAME CEIL_MB cmd args...  (through launch_lite.sh)
NAME=$1; CEIL=$2; shift 2
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
bash "${LAUNCH_LITE:?set LAUNCH_LITE to code/tools/launch_lite.sh}" $CEIL $D/logs2 $NAME "$@" >/dev/null 2>&1
echo "== $NAME: $(tail -1 $D/logs2/$NAME.watch)"
