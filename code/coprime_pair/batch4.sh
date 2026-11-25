#!/bin/bash
D="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
echo "== cert at tau=G(N) for the GW pairs (only m=(2,2) may be an exception; (2,3) has ML >= G)"
for T in "73 3 221 70 72" "283 3 851 280 282" "493 3 1481 490 492" "703 3 2111 700 702" "865 3 2597 858 864"; do set -- $T; echo "N=$1 tau=$2/$3"; $D/bin/cert2 $1 $2 $3 one $4 $5 | cut -c1-200 | tail -4; done
echo "== x2v 4..300000 (survivors and why they fail)"; $D/bin/x2v 4 300000 | grep -E "SURVIVOR|TIGHT|DONE" | cut -c1-420
echo "== cert3 (gcd>1 pairs only) N=247..300 level 2/(2N+1)"; $D/bin/loopcertg.sh 247 300 G 6
