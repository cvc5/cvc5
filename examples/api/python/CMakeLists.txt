set(EXAMPLES_API_PYTHON
  exceptions
)

find_package(PythonInterp REQUIRED)

# Find Python bindings in the corresponding python-*/site-packages directory.
# Lookup Python module directory and store path in PYTHON_MODULE_PATH.
execute_process(COMMAND
                  ${PYTHON_EXECUTABLE} -c
                    "from distutils.sysconfig import get_python_lib;\
                     print(get_python_lib(plat_specific=True,\
                             prefix='${CMAKE_PREFIX_PATH}/../..'))"
                OUTPUT_VARIABLE PYTHON_MODULE_PATH
                OUTPUT_STRIP_TRAILING_WHITESPACE)

foreach(example ${EXAMPLES_API_PYTHON})
  set(example_test example/api/python/${example})
  add_test(
    NAME ${example_test}
    COMMAND
      "${PYTHON_EXECUTABLE}" "${CMAKE_SOURCE_DIR}/api/python/${example}.py"
  )
  set_tests_properties(${example_test} PROPERTIES
    LABELS "example"
    ENVIRONMENT PYTHONPATH=${PYTHON_MODULE_PATH})
endforeach()
