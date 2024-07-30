###############################################################################
# Top contributors (to current version):
#   Andres Noetzli, Alex Ozdemir, Vinícius Camillo
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
  parser
  parser_sym_manager
  quickstart
  relations
  sequences
  sets
  strings
  sygus-fun
  sygus-inv
  transcendentals
  uf
)

find_package(Python ${CVC5_BINDINGS_PYTHON_VERSION} EXACT REQUIRED)

# Check whether the cvc5 module is already installed
execute_process(
  COMMAND ${Python_EXECUTABLE} -c "import cvc5"
  RESULT_VARIABLE PYTHON_CVC5_RC
  ERROR_QUIET
)

if(NOT (PYTHON_CVC5_RC EQUAL 0))
  # Find Python bindings in the corresponding python-*/site-packages directory.
  # Lookup Python module directory and store path in PYTHON_MODULE_PATH.
  execute_process(COMMAND
  ${Python_EXECUTABLE} -c
    "import os.path; import sysconfig;\
     print(os.path.dirname(os.path.dirname('${CMAKE_PREFIX_PATH}'))+\
     sysconfig.get_paths()['platlib'].split(sysconfig.get_config_var('platbase'))[1])"
  OUTPUT_VARIABLE PYTHON_MODULE_PATH
  OUTPUT_STRIP_TRAILING_WHITESPACE)
endif()

function(create_python_example example)
  set(example_test example/api/python/${example})
  add_test(
    NAME ${example_test}
    COMMAND
      "${Python_EXECUTABLE}" "${CMAKE_SOURCE_DIR}/api/python/${example}.py"
  )
  set_tests_properties(${example_test} PROPERTIES
    LABELS "example"
    ENVIRONMENT PYTHONPATH=${PYTHON_MODULE_PATH})
endfunction()

foreach(example ${EXAMPLES_API_PYTHON})
  create_python_example(${example})
endforeach()

if(CVC5_USE_COCOA)
  create_python_example("finite_field")
endif()
