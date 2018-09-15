set(EXAMPLES_API_BIN_DIR ${EXAMPLES_BIN_DIR}/api)

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
  add_executable(${example} EXCLUDE_FROM_ALL ${example}.cpp)
  target_link_libraries(${example} cvc4)
  set_target_properties(${example}
    PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${EXAMPLES_API_BIN_DIR})
  add_dependencies(examples ${example})
endforeach()

if(BUILD_BINDINGS_JAVA)
  add_subdirectory(java)
endif()
