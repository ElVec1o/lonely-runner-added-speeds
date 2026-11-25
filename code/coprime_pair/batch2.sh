#!/bin/bash
D="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
echo "== gw2 4..2000"; $D/bin/gw2 4 2000
echo "== gw2 4..10^7 (summary + first 40 lines + type census)"; $D/bin/gw2 4 10000000 > $D/logs/gw2_1e7.full; head -1 $D/logs/gw2_1e7.full; tail -1 $D/logs/gw2_1e7.full; grep -c "^N=" $D/logs/gw2_1e7.full; grep "^N=" $D/logs/gw2_1e7.full | head -40
echo "== type census (s1,s2,g,mu1,mu2) counts"; grep "^N=" $D/logs/gw2_1e7.full | sed -E 's/^N=[0-9]+ r=[0-9]+,[0-9]+ \(s=([0-9]+),([0-9]+)\) g=([0-9]+) mu=([0-9]+),([0-9]+) sets=([0-9]+)/s=\1,\2 g=\3 mu=\4,\5 sets=\6/' | sort | uniq -c | sort -rn | head -60
