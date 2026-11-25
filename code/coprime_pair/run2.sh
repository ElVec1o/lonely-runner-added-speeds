#!/bin/bash
# usage: run2.sh NAME bin args... -> launch_lite.sh, 500 MB ceiling
NAME=$1; BIN=$2; shift 2
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
bash "${LAUNCH_LITE:?set LAUNCH_LITE to code/tools/launch_lite.sh}" 500 $D/logs $NAME $D/bin/$BIN "$@" >/dev/null 2>&1
echo "== $NAME: $(tail -1 $D/logs/$NAME.watch)"; tail -${TAILN:-5} $D/logs/$NAME.out | cut -c1-600; head -3 $D/logs/$NAME.err
