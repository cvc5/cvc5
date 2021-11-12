# solver=cvc4
solver=./alethe-check.sh
options="--lang=smt2 --dag-thresh=0"
traces=""
time=""
ulimit="ulimit -S -t 10"
file="isabelle-int-real-mix.txt"
path="/home/hbarbosa/cvc/wt-diff/"

echo "Options: $options"
echo "Traces: $traces"
echo

while read name; do
    echo "$solver on $path$name";
    $ulimit; $time $solver "$path$name" $options $traces;
    echo "=====================================";
done < $file
