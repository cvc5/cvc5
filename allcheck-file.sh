# solver="./prod/bin/cvc5"
solver="./alethe-check.sh"
# options="--lang smt2 --dump-proofs --proof-format=alethe --proof-granularity=theory-rewrite "
options="--lang smt2"
# time="PATH=/usr/bin/:$PATH;"
ulimit="ulimit -S -t 30"
# file="qfuflia-liageneric.txt"

# echo $1
# echo "Options: $options"
# echo

while read name; do
    (echo "$solver on $name";
     $ulimit; time $solver $name $options;
     echo "==================="
    ) &>> "$1"_20221019.txt
done < $1
