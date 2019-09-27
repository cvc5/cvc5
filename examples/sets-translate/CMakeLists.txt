if(Boost_FOUND)
  cvc4_add_example(sets2arrays
    "sets_translate.cpp" "sets-translate"
    # argument to binary (for testing)
    ${CMAKE_CURRENT_SOURCE_DIR}/sets-translate-example-input.smt2)

  cvc4_add_example(sets2axioms
    "sets_translate.cpp" "sets-translate"
    # argument to binary (for testing)
    ${CMAKE_CURRENT_SOURCE_DIR}/sets-translate-example-input.smt2)
  target_compile_definitions(sets2axioms PRIVATE -DENABLE_AXIOMS)
endif()

