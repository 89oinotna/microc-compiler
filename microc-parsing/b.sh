#!/bin/bash
touch t.txt;
for f in test/*.mc;
do
./microcc $f >> echo >> t.txt
done;
