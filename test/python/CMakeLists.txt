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
      "Could not find pytest for Python "
      "version ${PYTHON_VERSION_MAJOR}.${PYTHON_VERSION_MINOR}. "
      "Make sure to install pytest for this Python version "
      "via \n`${PYTHON_EXECUTABLE} -m pip install pytest'.\nNote: You need to "
      "have pip installed for this Python version.")
endif()

macro(cvc4_add_python_api_test name filename)

  #   we create test target 'python/unit/api/myapitest'
  #   and run it with 'ctest -R "python/unit/api/myapitest"'.
  add_test (NAME python/unit/api/${name}
    COMMAND ${PYTHON_EXECUTABLE} -m pytest ${CMAKE_CURRENT_SOURCE_DIR}/${filename}
    # directory for importing the python bindings
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/src/api/python)

endmacro()

# add specific test files
cvc4_add_python_api_test(pytest_solver unit/api/test_solver.py)
