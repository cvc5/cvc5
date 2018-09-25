#!/bin/bash

# Copyright (C) 2017  Mate Soos
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; version 2
# of the License.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
# 02110-1301, USA.

if [[ $# -ne 3 ]]; then
    echo "ERROR: wrong number of arguments"
    echo "Use with ./predict_one.sh 6s153.cnf.gz DIR RATIO"
    echo "for ex.  ./predict_one.sh 6s153.cnf.gz mydir 0.5"
    exit -1
fi
set -e
set -x

status=$(./cryptominisat5 --hhelp | grep sql)
ret=$?
if [ "$ret" -ne 0 ]; then
    echo "You must compile SQL into cryptominisat"
    exit -1
fi

FNAME=$1
OUTDIR=$2
RATIO=$3
mkdir -p "${OUTDIR}"

rm -if "${OUTDIR}/drat_out"
rm -if "${OUTDIR}/clause_id_data"
rm -if "${OUTDIR}/data.sqlite"
rm -if "${OUTDIR}/data.sqlite.tree.dot"
echo "Predicting file $1"

# running CNF
./cryptominisat5 ${FNAME} --cldatadumpratio "${RATIO}" --gluecut0 10000 --presimp 1 -n 1 --zero-exit-status --restart luby --clid --sql 2 --maple 0 --distill 0 --sqlitedb "${OUTDIR}/data.sqlite" "${OUTDIR}/drat_out" > "${OUTDIR}/cms_output.txt"

# parse DRAT for UNSAT proof data
./tests/drat-trim/drat-trim "${FNAME}" "${OUTDIR}/drat_out" -x "${OUTDIR}/clause_id_data" -i

# add clause IDs and their age and performance data
./add_lemma_ind.py "${OUTDIR}/data.sqlite" "${OUTDIR}/clause_id_data"

# get pandas dataframe from SQLite database
./gen_pandas.py --csv "${OUTDIR}/data.sqlite"

# generate predictors
./predict.py "${OUTDIR}/data.sqlite-pandasdata.dat" --dot "${OUTDIR}/dectree.dot"

# generate DOT and display it
dot -Tpng "${OUTDIR}/dectree.dot" -o tree.png
display tree.png
