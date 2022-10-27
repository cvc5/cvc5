solver="./alethe-check.sh"
options=""
options=""
time=""
ulimit="ulimit -S -t 30"
# file="qflia-liageneric-nocutlemmas.txt"
# file="qflia-liageneric.txt"
file="qfuflia-liageneric.txt"

echo "Options: $options"
echo

while read name; do
    echo "$solver on $name";
    $ulimit; $time $solver $name $options;
    echo "=====================================";
done < $file
