set(CVC4_EXAMPLES_API
  bitvectors
  bitvectors_and_arrays
  combination
  datatypes
  extract
  helloworld
  linear_arith
  sets
  strings
  sygus-fun
  sygus-grammar
  sygus-inv
)

foreach(example ${CVC4_EXAMPLES_API})
  cvc4_add_example(${example} "" "api")
endforeach()
