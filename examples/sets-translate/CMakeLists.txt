set(EXAMPLES_SETS_TRANSLATE_BIN_DIR ${EXAMPLES_BIN_DIR}/sets-translate) 

add_executable(sets2arrays EXCLUDE_FROM_ALL sets_translate.cpp)
target_link_libraries(sets2arrays cvc4 cvc4parser)

add_executable(sets2axioms EXCLUDE_FROM_ALL sets_translate.cpp)
target_compile_definitions(sets2axioms PRIVATE -DENABLE_AXIOMS)
target_link_libraries(sets2axioms cvc4 cvc4parser)

set_target_properties(sets2arrays sets2axioms
  PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${EXAMPLES_SETS_TRANSLATE_BIN_DIR})
