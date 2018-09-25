#!/bin/sh
set -x

zgrep "CPU" *out.gz | awk '{if ($5 < 1500) {print $1}}' | sed 's/:c.*$//' | sort > solved_under_1500_full_list

zgrep "CPU time" *out.gz | awk '{print $5}' > solveTimes
zgrep "CPU time" *out.gz | awk '{print $1}' | sed 's/:c$//' | sed 's/gz.*/gz/' | sort  > solved
ls *.out.gz | sed 's/gz.*/gz/' | sort > allFiles
zgrep "s UNSATISFIABLE" *out.gz | sed 's/:s.*$//' | sed 's/gz.*/gz/' | sort > solvedUNSAT
zgrep "s SATISFIABLE" *out.gz   | sed 's/:s.*$//' | sed 's/gz.*/gz/' | sort > solvedSAT


zgrep "s.*SATISFIABLE" $(cat solved_under_1500_full_list) | sed 's/:s.*$//' | sed 's/gz.*/gz/' | sort > solved1500
zgrep "s.* UNSATISFIABLE" $(cat solved_under_1500_full_list) | sed 's/:s.*$//' | sed 's/gz.*/gz/' | sort > solvedUNSAT1500
zgrep "s.* SATISFIABLE" $(cat solved_under_1500_full_list)   | sed 's/:s.*$//' | sed 's/gz.*/gz/' | sort > solvedSAT1500
rm solved_under_1500_full_list
