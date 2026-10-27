# cvc5 API Examples

This directory contains usage examples of cvc5's different language
bindings, library APIs, and also tutorial examples from the tutorials
available at http://cvc4.cs.stanford.edu/wiki/Tutorials

## Building Examples

The examples provided in this directory are not built by default.
First, build cvc5 and install it in your system.
To do so, follow [these](https://github.com/cvc5/cvc5/blob/main/INSTALL.rst) instructions.

Then, proceed as follows:
```
  mkdir <build_dir>
  cd <build_dir>
  cmake ..
  make               # use -jN for parallel build with N threads

  ctest              # run all examples
  ctest -R <example> # run specific example '<example>'

  # Or just run the binaries in directory <build_dir>/bin/, for example:
  bin/api/bitvectors
```

**Note:** If you installed cvc5 in a non-standard location you have to
additionally specify `CMAKE_PREFIX_PATH` to point to the location of
`cvc5Config.cmake` (usually `<your-install-prefix>/lib/cmake`) as follows:

```
  cmake .. -DCMAKE_PREFIX_PATH=<your-install-prefix>/lib/cmake
```

The examples binaries are built into directory `<build_dir>/bin`, e.g.,
`<build_dir>/bin/api/cpp/bags` for `api/cpp/bags.cpp`.

**Note:** The binaries for the C examples in `api/c` are renamed with a `c_`
          prefix, e.g., `<build_dir>/bin/api/c/c_bags` for `api/c/bags.c`.

## SimpleVC*, simple_vc*

These are examples of how to use cvc5 with each of its library
interfaces (APIs) and language bindings.  They are essentially "hello
world" examples, and do not fully demonstrate the interfaces, but
function as a starting point to using simple expressions and solving
functionality through each library.

## Targeted examples

The `api` directory contains some more specifically-targeted examples (for
bit-vectors, for arithmetic, etc.) for each supported language binding and
their corresponding encodings in SMT-LIB.
