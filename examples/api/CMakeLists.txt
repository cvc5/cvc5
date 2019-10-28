set(CVC4_EXAMPLES_API
  bitvectors
  bitvectors-new
  bitvectors_and_arrays
  bitvectors_and_arrays-new
  combination
  combination-new
  datatypes
  datatypes-new
  extract
  extract-new
  helloworld
  helloworld-new
  linear_arith
  linear_arith-new
  sets
  sets-new
  strings
  strings-new
)

foreach(example ${CVC4_EXAMPLES_API})
  cvc4_add_example(${example} "" "api")
endforeach()
