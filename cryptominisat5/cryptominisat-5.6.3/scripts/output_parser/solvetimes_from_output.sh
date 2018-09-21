#!/bin/sh

#set -x

grep --color -i "assert.*fail" `ls *.out`
grep --color -i signal `ls *.out`
grep --color -i error `ls *.out`
grep --color -i terminate `ls *.out`
grep --color -i abort `ls *.out` | grep -v expensive
grep --color -i failed `ls *.out` | grep -v probes

ls -- *out | sed 's/gz.*/gz/' > allFiles

# 1500 cutoff
grep "Total" *out | awk '{print $5}' > solveTimes
grep "Total" *out | awk '{if ($5 < 1500) {print $1}}' | sed 's/:c.*$//' | sort > solved_under_1500_full_list


# for normal
grep "s.*SATISFIABLE" *out | sed 's/:s.*$//' | sed 's/gz.*/gz/' | sort > solved
grep "s UNSATISFIABLE" *out | sed 's/:s.*$//' | sed 's/gz.*/gz/' | sort > solvedUNSAT
grep "s SATISFIABLE" *out   | sed 's/:s.*$//' | sed 's/gz.*/gz/' | sort > solvedSAT

# 1500 cutoff
grep "s.*SATISFIABLE" $(cat solved_under_1500_full_list) | sed 's/:s.*$//' | sed 's/gz.*/gz/' | sort > solved1500
grep "s UNSATISFIABLE" $(cat solved_under_1500_full_list) | sed 's/:s.*$//' | sed 's/gz.*/gz/' | sort > solvedUNSAT1500
grep "s SATISFIABLE" $(cat solved_under_1500_full_list)   | sed 's/:s.*$//' | sed 's/gz.*/gz/' | sort > solvedSAT1500
rm solved_under_1500_full_list
