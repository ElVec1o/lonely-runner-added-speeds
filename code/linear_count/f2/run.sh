#!/bin/bash
# usage: run.sh NAME args... -> launch_lite.sh, ceiling 300 MB
NAME=$1; shift
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
bash "${LAUNCH_LITE:?set LAUNCH_LITE to code/tools/launch_lite.sh}" 300 $D/logs $NAME $D/bin/f2 "$@" >/dev/null 2>&1
echo "== $NAME: $(tail -1 $D/logs/$NAME.watch)"; cut -c1-${W:-600} $D/logs/$NAME.out | tail -${TAILN:-40}
