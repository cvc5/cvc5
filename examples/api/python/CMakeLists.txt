#####################
## CMakeLists.txt
## Top contributors (to current version):
##   Andres Noetzli
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
set(EXAMPLES_API_PYTHON
  bitvectors_and_arrays
  bitvectors
  combination
  datatypes
  exceptions
  extract
  floating_point
  helloworld
  linear_arith
  sequences
  sets
  strings
  sygus-fun
  sygus-grammar
  sygus-inv
)

find_package(PythonInterp ${CVC4_BINDINGS_PYTHON_VERSION} REQUIRED)

# Find Python bindings and store path in PYTHON_MODULE_PATH.
# NOTE can't count on Python's distutils.sysconfig.get_python_lib
# to work correctly with CMAKE_PREFIX_PATH because the C++ libs
# are in lib64 on some systems, while the python modules get put
# in lib
execute_process(COMMAND
                  find ${CMAKE_PREFIX_PATH}/../../ -name "pycvc4" -type d
                OUTPUT_VARIABLE PYTHON_MODULE_PATH
                OUTPUT_STRIP_TRAILING_WHITESPACE
                )

message("Got PYTHON_MODULE_PATH=${PYTHON_MODULE_PATH}")
foreach(example ${EXAMPLES_API_PYTHON})
  set(example_test example/api/python/${example})
  add_test(
    NAME ${example_test}
    COMMAND
      printenv PYTHONPATH && ls ${PYTHON_MODULE_PATH} && "${PYTHON_EXECUTABLE}" "${CMAKE_SOURCE_DIR}/api/python/${example}.py"
  )
  set_tests_properties(${example_test} PROPERTIES
    LABELS "example"
    ENVIRONMENT PYTHONPATH=${PYTHON_MODULE_PATH})
endforeach()
