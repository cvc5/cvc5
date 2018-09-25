#!/bin/bash
set -e
set -x

rm -f mergeddata.sqlite
FNAME=todo
rm -f $FNAME
echo ".read /home/soos/development/sat_solvers/cryptominisat/cmsat_tablestructure.sql" >> $FNAME
for FILE in *sqlite*; do
	echo "attach '${FILE}' as tomerge;" >> $FNAME
	myarray=( tags timepassed memused reduceDB finishup )
	for DAT in "${myarray[@]}"; do
		echo "insert into ${DAT} select * from tomerge.${DAT};" >> $FNAME;
	done
	echo "detach tomerge;" >> $FNAME
done
sqlite3 mergeddata.sqlite < $FNAME

# rm -f dump
# rm -f schema
# for FILE in *sqlite*; do
# 	sqlite3 "$FILE" .sch > schema
# 	sqlite3 "$FILE" .dump | grep INSERT | sed 's/\"//g' > dump
# done
