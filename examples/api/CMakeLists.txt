set(EXAMPLES_API_BIN_DIR ${EXAMPLES_BIN_DIR}/api) 

foreach(example ${CVC4_EXAMPLES_API})
  add_executable(${example} EXCLUDE_FROM_ALL ${example}.cpp)
  target_link_libraries(${example} cvc4)
  set_target_properties(${example}
    PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${EXAMPLES_API_BIN_DIR})
endforeach()

if(BUILD_BINDINGS_JAVA)
  add_subdirectory(java)
endif()
