###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Aina Niemetz, Yoni Zohar
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

# Check if the pytest Python module is installed.
check_python_module("pytest")

# Add Python bindings API unit tests.
macro(cvc5_add_python_api_unit_test name filename)
# We create test target 'unit/api/python/myapitest' and run it with
# 'ctest -R "unit/api/python/myapitest"'.
  set(test_name unit/api/python/${name})
  add_test (NAME ${test_name}
    COMMAND ${Python_EXECUTABLE}
            -m pytest ${CMAKE_CURRENT_SOURCE_DIR}/${filename}
    # directory for importing the python bindings
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/src/api/python)
    set_tests_properties(${test_name} PROPERTIES LABELS "unit;python")
endmacro()

# add specific test files
if(USE_COCOA)
  cvc5_add_python_api_unit_test(test_finite_field test_finite_field.py)
endif()
cvc5_add_python_api_unit_test(test_solver test_solver.py)
cvc5_add_python_api_unit_test(test_sort test_sort.py)
cvc5_add_python_api_unit_test(test_term test_term.py)
cvc5_add_python_api_unit_test(test_datatype_api test_datatype_api.py)
cvc5_add_python_api_unit_test(test_grammar test_grammar.py)
cvc5_add_python_api_unit_test(test_to_python_obj test_to_python_obj.py)
cvc5_add_python_api_unit_test(test_op test_op.py)
cvc5_add_python_api_unit_test(test_result test_result.py)
cvc5_add_python_api_unit_test(test_synth_result test_synth_result.py)

cvc5_add_unit_test_black(test_uncovered api/python)
