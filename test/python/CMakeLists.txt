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
check_python_module("pytest")

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
