# Notes

These files are copied from [the pythonic API's repository](https://github.com/cvc5/cvc5_pythonic_api).

They were copied with this script:

    for f in ~/$CVC_PYTHONIC/test/pgms/example_*; do; ff=$(echo ${f:t} | sed 's/example_//'); cat $f | sed 's/_pythonic_api/.pythonic/' > examples/api/python/pythonic/$ff ; done;

Notice that the script fixes up the import statements to align with a version
of the cvc5 python APIs that are packaged together.
