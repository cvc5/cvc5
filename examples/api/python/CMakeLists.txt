###############################################################################
# Top contributors (to current version):
#   Andres Noetzli, Yoni Zohar, Mudathir Mohamed
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

set(EXAMPLES_API_PYTHON
  bags
  bitvectors_and_arrays
  bitvectors
  combination
  datatypes
  exceptions
  extract
  floating_point
  helloworld
  id
  linear_arith
  quickstart
  relations
  sequences
  sets
  strings
  sygus-fun
  sygus-inv
  transcendentals
)

find_package(Python ${CVC5_BINDINGS_PYTHON_VERSION} EXACT REQUIRED)

# Find Python bindings in the corresponding python-*/site-packages directory.
# Lookup Python module directory and store path in PYTHON_MODULE_PATH.
execute_process(COMMAND
                  ${Python_EXECUTABLE} -c
                    "from distutils.sysconfig import get_python_lib;\
                     print(get_python_lib(plat_specific=True,\
                             prefix='${CMAKE_PREFIX_PATH}/../..'))"
                OUTPUT_VARIABLE PYTHON_MODULE_PATH
                OUTPUT_STRIP_TRAILING_WHITESPACE)

function(create_python_example example)
  set(example_test example/api/python/${example})
  add_test(
    NAME ${example_test}
    COMMAND
      "${Python_EXECUTABLE}" "${CMAKE_SOURCE_DIR}/api/python/${example}.py"
  )
  set_tests_properties(${example_test} PROPERTIES
    LABELS "example"
    ENVIRONMENT PYTHONPATH=${PYTHON_MODULE_PATH}:${CMAKE_SOURCE_DIR}/api/python)
endfunction()

foreach(example ${EXAMPLES_API_PYTHON})
  create_python_example(${example})
endforeach()

if(USE_COCOA)
  create_python_example("finite_field")
endif()
