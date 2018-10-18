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

set(EXAMPLES_API_LINK_LIBS cvc4 cvc4parser)
foreach(example ${CVC4_EXAMPLES_API})
  cvc4_add_example(${example}
    "" "${EXAMPLES_API_LINK_LIBS}" "api")
endforeach()

if(BUILD_BINDINGS_JAVA)
  add_subdirectory(java)
endif()
