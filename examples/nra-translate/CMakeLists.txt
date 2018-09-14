set(EXAMPLES_NRA_TRANSLATE_BIN_DIR ${EXAMPLES_BIN_DIR}/nra-translate) 

foreach(example ${CVC4_EXAMPLES_NRA_TRANSLATE})
  add_executable(${example} EXCLUDE_FROM_ALL ${example}.cpp)
  target_link_libraries(${example} cvc4 cvc4parser)
  set_target_properties(${example}
    PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${EXAMPLES_NRA_TRANSLATE_BIN_DIR})
endforeach()
