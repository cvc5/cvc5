###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Aina Niemetz, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

# Check if the pytest Python module is installed.
check_python_module("pytest")

# Add Python bindings API tests.
macro(cvc5_add_python_api_test name filename)
# We create test target 'python/unit/api/myapitest' and run it with
# 'ctest -R "python/unit/api/myapitest"'.
add_test (NAME python/unit/api/${name}
  COMMAND ${PYTHON_EXECUTABLE} -m pytest ${CMAKE_CURRENT_SOURCE_DIR}/${filename}
  # directory for importing the python bindings
  WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/src/api/python)
endmacro()

# add specific test files
cvc5_add_python_api_test(pytest_solver unit/api/test_solver.py)
cvc5_add_python_api_test(pytest_sort unit/api/test_sort.py)
cvc5_add_python_api_test(pytest_term unit/api/test_term.py)
cvc5_add_python_api_test(pytest_grammar unit/api/test_grammar.py)
