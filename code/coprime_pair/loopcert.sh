#!/bin/bash
# usage: loopcert.sh NMIN NMAX Gmode(G|I) KEEP ; runs cert all for each N; prints EXC/FLAG/POINT/R= lines and one DONE line per N with time
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
for ((N=$1; N<=$2; N++)); do
  if [ "$3" = G ]; then P=2; Q=$((2*N+1)); else P=1; Q=$N; fi
  S=$(date +%s); $D/bin/cert $N $P $Q all | grep -v '^progress' | cut -c1-240 | tail -${4:-6}; echo "   (N=$N time $(( $(date +%s)-S ))s)"
done
