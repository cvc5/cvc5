#!/bin/sh

zgrep "\%.*all" -- *out.gz | awk '{print $2}' > solveTimes
zgrep "\% *all" -- *out.gz | awk '{print $1}' | sed 's/:c$//' | sed 's/gz.*/gz/' | sort > solved
ls -- *out.gz | sed 's/gz.*/gz/' | sort > allFiles
zgrep "s UNSATISFIABLE" -- *out.gz | sed 's/:s.*$//' | sed 's/gz.*/gz/' | sort > solvedUNSAT
zgrep "s SATISFIABLE" -- *out.gz   | sed 's/:s.*$//' | sed 's/gz.*/gz/' | sort > solvedSAT
