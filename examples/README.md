# CVC4 API Examples

This directory contains usage examples of CVC4's different language
bindings, library APIs, and also tutorial examples from the tutorials
available at http://cvc4.cs.stanford.edu/wiki/Tutorials

## Building Examples

The examples provided in this directory are not built by default.

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

**Note:** If you installed CVC4 in a non-standard location you have to
additionally specify `CMAKE_PREFIX_PATH` to point to the location of
`CVC4Config.cmake` (usually `<your-install-prefix>/lib/cmake`) as follows:

```
  cmake .. -DCMAKE_PREFIX_PATH=<your-install-prefix>/lib/cmake
```

The examples binaries are built into `<build_dir>/bin`.

## SimpleVC*, simple_vc*

These are examples of how to use CVC4 with each of its library
interfaces (APIs) and language bindings.  They are essentially "hello
world" examples, and do not fully demonstrate the interfaces, but
function as a starting point to using simple expressions and solving
functionality through each library.

## Targeted examples

The "api" directory contains some more specifically-targeted
examples (for bitvectors, for arithmetic, etc.).  The "api/java"
directory contains the same examples in Java.
