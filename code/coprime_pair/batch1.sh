#!/bin/bash
D="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
echo "== lemz"; $D/bin/lemz 4 3000
echo "== lemf control=0"; $D/bin/lemf 5 22 40 400 0 | tail -12
echo "== lemf control=1 (negative control: (b) strengthened by 1)"; $D/bin/lemf 5 22 40 400 1 | tail -4
echo "== cert ctl (pieces vs exact ML), level 2/(2N+1) and 1/N"
for N in 6 7 8 9 10 11 12; do $D/bin/cert2 $N 2 $((2*N+1)) ctl 45 | tail -2; $D/bin/cert2 $N 1 $N ctl 45 | tail -2; done
echo "== cert boundary control: N=73 R=70,72 tau=1/74 (ML=1/74 set must NOT be an exception)"; $D/bin/cert2 73 1 74 one 70 72 | tail -3
echo "== cert N=73 R=70,72 tau=2/147 (planted positives)"; $D/bin/cert2 73 2 147 one 70 72 | tail -7
