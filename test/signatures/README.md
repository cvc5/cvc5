# Signature Tests

This directory contains tests of our LFSC proof signatures. To run just the
tests in this directory, the test label `signatures` can be used (`ctest -L
signatures`).

## Adding a New Signature Test

To add a new signature test file, add the file to git, for example:

```
git add test/signatures/new_signature_test.plf
```

Also add it to [CMakeLists.txt](CMakeLists.txt) in this directory and declare
the dependencies of the test as explained below.

The signature tests are prefixed with `signatures/`, so the test for
`example.plf` will have the name `signatures/example.plf`.

## Test Dependencies

Tests can declare the signature files that they depend on using the `; Deps:`
directive followed by a space-separated list of files. For example:

```
; Deps: sat.plf smt.plf
```

indicates that the test depends on `sat.plf` and `smt.plf`. The run script
automatically searches for the listed files in `proofs/signatures` as well as
the directory of the test input.
