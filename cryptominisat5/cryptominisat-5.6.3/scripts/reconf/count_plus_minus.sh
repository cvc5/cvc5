#!/usr/bin/bash

#rm outfile*.data
#rm outs/*.data
#./reconf.py -n 18 -i 1,2,8,9,10,11,15,5,14,13,3 -f outs/out /home/soos/media/sat/out/new/out-reconf-6776906.wlm01-*/*.out


for f in `ls outs/*.data`; do
    echo "$f:"
    grep ",+" $f  | wc -l;
    grep ",-" $f  | wc -l;
    echo "---"
done


echo "this is solved by everyone:"
grep "total-10-13-u.cnf" outs/*.data

echo "this is solved by nobody:"
grep "partial-10-13-u.cnf" outs/*.data

echo "this is solved by some only -8-==rec15 and -10-=rec17 and -9-=rec16), small diff:"
grep "mp1-22.5.cnf.gz" outs/*.data

echo "this is solved by everyone except 7, large diff:"
grep "mp1-klieber2017s-1000-024-eq.cnf" outs/*.data

echo "given    neg : rec17, rec7, rec16"
echo "which is eqiv: 10, 4, 9, (note: 8-drat = 15, which is ignored)"

echo "to check:"
echo 'grep -i "User time"  */mp1-klieber2017s-1000-024-eq.cnf*.timeout | awk '{print $5 " -- " $1}' | sort -n'

echo 'mapping:
num -> reconf
0      0
1      3
2      4
3      6
4      7
5      12
6      13
7      14
8      15
9      16
10     17'
