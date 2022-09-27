solver="./prod/bin/cvc5"
options="--lang smt2 --dump-proofs --proof-format=alethe --proof-granularity=theory-rewrite "
traces=""
time=""
ulimit="ulimit -S -t 5"
file="qf-liageneric.txt"

echo "Options: $options"
echo "Traces: $traces"
echo

while read name; do
    echo "$solver on $name";
    $ulimit; $time $solver $options $traces $name > $name.cvc5proof;
    echo "=====================================";
done < $file
