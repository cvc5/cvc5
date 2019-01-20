set(EXAMPLES_API_PYTHON
  exceptions
)

foreach(example ${EXAMPLES_API_PYTHON})
  set(example_test example/api/python/${example})
  add_test(
    NAME ${example_test}
    COMMAND
      "${PYTHON_EXECUTABLE}" "${CMAKE_SOURCE_DIR}/examples/api/python/${example}.py"
  )
  set_tests_properties(${example_test} PROPERTIES
    LABELS "example"
    ENVIRONMENT PYTHONPATH=${CMAKE_BINARY_DIR}/src/bindings/python)
endforeach()
