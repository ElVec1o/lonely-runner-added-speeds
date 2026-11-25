#!/bin/bash
# usage: run.sh CEIL NAME args... -> launch_lite.sh (
CEIL=$1; NAME=$2; shift 2
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
bash "${LAUNCH_LITE:?set LAUNCH_LITE to code/tools/launch_lite.sh}" $CEIL $D/logs $NAME $D/bin/lcov "$@" >/dev/null 2>&1
echo "== $NAME: $(tail -2 $D/logs/$NAME.watch | tr '\n' ' ')"; cut -c1-300 $D/logs/$NAME.out | head -${LINES_OUT:-70}
