set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin/examples/nra-translate)

foreach(example ${CVC4_EXAMPLES_NRA_TRANSLATE})
  add_executable(${example} EXCLUDE_FROM_ALL ${example}.cpp)
  target_link_libraries(${example} cvc4 cvc4parser)
endforeach()
