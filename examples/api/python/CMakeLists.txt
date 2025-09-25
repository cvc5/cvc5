###############################################################################
# Top contributors (to current version):
#   Daniel Larraz, Andres Noetzli, Andrew Reynolds
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

set(EXAMPLES_API_PYTHON
  bitvectors_and_arrays
  bitvectors
  combination
  datatypes
  exceptions
  extract
  helloworld
  id
  linear_arith
  parser
  parser_sym_manager
  quickstart
  sequences
  sets
  strings
  sygus-fun
  sygus-inv
  uf
)

# Examples that have a Pythonic version.
# This list should include any such example,
# even if it is only conditionally added (e.g.,
# based on CVC5_USE_COCOA or NOT CVC5_SAFE_BUILD).
set(EXAMPLES_API_PYTHON_PYTHONIC
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
  sequences
  sets
  strings
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

function(_add_python_test example subdir)
  string(REPLACE "/" "_" subdir_name "${subdir}") # unique test name
  set(test_name example/${subdir_name}/${example})

  add_test(
    NAME     ${test_name}
    COMMAND  "${Python_EXECUTABLE}"
             "${CMAKE_SOURCE_DIR}/${subdir}/${example}.py"
  )
  set_tests_properties(${test_name} PROPERTIES
    LABELS      "example"
    ENVIRONMENT "PYTHONPATH=${PYTHON_MODULE_PATH}"
  )
endfunction()

function(create_python_example example)
  # Base Python API example
  _add_python_test(${example} "api/python")

  # Only add the Pythonic version if it is in the list
  if (example IN_LIST EXAMPLES_API_PYTHON_PYTHONIC)
    _add_python_test(${example} "api/python/pythonic")
  endif()
endfunction()

foreach(example ${EXAMPLES_API_PYTHON})
  create_python_example(${example})
endforeach()

if((NOT CVC5_SAFE_BUILD) AND (NOT CVC5_STABLE_BUILD))
  create_python_example("floating_point")
  create_python_example("bags")
  create_python_example("relations")
  create_python_example("transcendentals")
endif()

if(CVC5_USE_COCOA)
  create_python_example("finite_field")
endif()
