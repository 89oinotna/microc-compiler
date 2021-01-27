#!/bin/bash
touch t.txt;
for f in test/*.mc;
do
NAME="$(basename -s .mc $f)";
echo $NAME;
echo $NAME >> t.txt;
./microcc $f -c;
llvm-link a.bc rt-support.bc -o o.bc;

MYOUT=$(lli o.bc); #>> echo >> t.txt;
#echo myout >> t.txt;
OUT=$(cat "test/$NAME.out") # >> t.txt;
diff <(echo "$MYOUT") <(echo "$OUT") >> t.txt
done;
