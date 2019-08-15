set(EXAMPLES_NRA_TRANSLATE_BIN_DIR ${EXAMPLES_BIN_DIR}/nra-translate)

set(CVC4_EXAMPLES_NRA_TRANSLATE
  normalize
  smt2info
  smt2todreal
  smt2toisat
  smt2tomathematica
  smt2toqepcad
  smt2toredlog
)

foreach(example ${CVC4_EXAMPLES_NRA_TRANSLATE})
  cvc4_add_example(${example} "" "nra-translate"
    # arguments to binary (for testing)
    # input file is required by all tests
    ${CMAKE_CURRENT_SOURCE_DIR}/nra-translate-example-input.smt2
    # This is a dummy argument for smt2toredlog (argument is only printed, can
    # be anything for testing purposes). We pass this to all examples since the
    # other examples ignore additional arguments.
    "foo")
endforeach()
