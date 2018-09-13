set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin/examples/api)

foreach(example ${CVC4_EXAMPLES_API})
  add_executable(${example} EXCLUDE_FROM_ALL ${example}.cpp)
  target_link_libraries(${example} cvc4)
endforeach()

if(BUILD_BINDINGS_JAVA)
  add_subdirectory(java)
endif()
