#!/bin/bash
# sums the per-N lines of a mm scan log: agg.sh logfile
grep '^N=' "$1" | sed 's/ | nontight.*//' | tr ' |' '\n\n' | awk -F'[=:]' '
/^sets=/{s+=$NF} /^ML>U/{a+=$NF} /^ML=U/{b+=$NF} /^ML<U/{c+=$NF} /^LBFAIL/{d+=$NF} /^max-witness==ML/{e+=$NF} /^witness<ML/{f+=$NF} /^crit&eq/{g+=$NF} /^!crit&eq/{h+=$NF} /^crit&!eq/{i+=$NF} /^!crit&!eq/{j+=$NF}
END{printf "sets=%d ML>U=%d ML=U=%d ML<U=%d LBFAIL=%d maxwit==ML=%d wit<ML=%d | crit&eq=%d !crit&eq=%d crit&!eq=%d !crit&!eq=%d\n",s,a,b,c,d,e,f,g,h,i,j}'
grep '^N=' "$1" | sed 's/.*nontight(U>1\/A): sets=\([0-9]*\) ML=U:\([0-9]*\)/\1 \2/' | awk '{a+=$1;b+=$2} END{printf "nontight(U>1/A) sets=%d of which ML=U=%d\n",a,b}'
