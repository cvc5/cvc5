#!/usr/bin/env bash
#/space/ajreynol/cvc5-ajr/proofs/alf/rules/drat/drat-trim $1 $2

#INPUT=$1
#PROOF=$2
#echo "parse"
# Emptying IFS supresses word splitting by Bash
# Using '"' in IFS makes bash drop the quotes
IFS= read -r line
if [[ "$line" != "(" ]]; then
      exit 1
fi
IFS='"' read -r drop INPUT
IFS= read -r line
if [[ "$line" != ")" ]]; then
      exit 1
fi
#echo "got input $INPUT"

#INPUT=`sed -e 's/^"//' -e 's/"$//' <<<"$INPUT"`
#PROOF=`sed -e 's/^"//' -e 's/"$//' <<<"$PROOF"`

#echo "RUN: drat-trim $INPUT $PROOF"
#echo "run cadical"
#cadical $INPUT $INPUT.proof > /dev/null
# without binary makes drat-trim fail sometimes
cadical $INPUT $INPUT.proof --binary=false > /dev/null
#echo "run drat-trim"
RESULT=$(cat $INPUT.proof | drat-trim $INPUT)
#echo "finished"
rm -f $INPUT.proof

if [[ $RESULT == *"s VERIFIED"* ]];
then
      echo "true"
      exit 0
else
      echo "error: $RESULT"
      exit 1
fi

