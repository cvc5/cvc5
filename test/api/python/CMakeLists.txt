#####################
## CMakeLists.txt
## Top contributors (to current version):
##   Makai Mann
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
#-----------------------------------------------------------------------------#
# Add Python bindings API tests

# Check if the pytest Python module is installed.
execute_process(
  COMMAND
  ${PYTHON_EXECUTABLE} -c "import pytest"
  RESULT_VARIABLE
    RET_PYTEST
  ERROR_QUIET
)

if(RET_PYTEST)
    message(FATAL_ERROR
      "Could not find Python module pytest. Install via `pip install pytest'.")
endif()

macro(cvc4_add_python_api_test name filename)

  #   we create test target 'api/<output_dir>/myapitest'
  #   and run it with 'ctest -R "api/<output_dir>/myapitest"'.
  add_test (NAME api/api/python/${name}
    COMMAND ${PYTHON_EXECUTABLE} -m pytest ${CMAKE_CURRENT_SOURCE_DIR}/${filename}
    # directory for importing the python bindings
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/src/api/python)

endmacro()

cvc4_add_python_api_test(pytest_datatype_api test_datatype_api.py)
cvc4_add_python_api_test(pytest_grammar test_grammar.py)
cvc4_add_python_api_test(pytest_sort test_sort.py)
cvc4_add_python_api_test(pytest_term test_term.py)
cvc4_add_python_api_test(pytest_to_python_obj test_to_python_obj.py)
