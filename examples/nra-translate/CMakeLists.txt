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
  add_executable(${example} EXCLUDE_FROM_ALL ${example}.cpp)
  target_link_libraries(${example} cvc4 cvc4parser)
  set_target_properties(${example}
    PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${EXAMPLES_NRA_TRANSLATE_BIN_DIR})
  add_dependencies(examples ${example})
endforeach()
