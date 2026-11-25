#!/bin/bash
D="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
for T in "283 280 282" "493 490 492" "703 700 702" "865 858 864"; do set -- $T; N=$1; S=$(date +%s); echo "== N=$N R=$2,$3 tau=2/(2N+1)"; $D/bin/cert2 $N 2 $((2*N+1)) one $2 $3 | cut -c1-260; echo "   (time $(( $(date +%s)-S ))s)"; done
