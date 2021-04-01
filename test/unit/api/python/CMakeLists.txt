#####################
## CMakeLists.txt
## Top contributors (to current version):
##   Makai Mann and Yoni Zohar
## This file is part of the CVC4 project.
## Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

  #   we create test target 'unit/api/python/myapitest'
  #   and run it with 'ctest -R "unit/api/python/myapitest"'.
  add_test (NAME unit/api/python/${name}
    COMMAND ${PYTHON_EXECUTABLE} -m pytest ${CMAKE_CURRENT_SOURCE_DIR}/${filename}
    # directory for importing the python bindings
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/src/api/python)

endmacro()

# add specific test files
cvc4_add_python_api_test(pytest_solver test_solver.py)
