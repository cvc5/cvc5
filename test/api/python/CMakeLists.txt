###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Alex Ozdemir, Vinícius Camillo
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

# Add Python bindings API tests.
macro(cvc5_add_python_api_test name filename)
# We create test target 'api/python/myapitest' and run it with
# 'ctest -R "api/python/myapitest"'.
  set(test_name api/python/${name})
  add_test (NAME ${test_name}
    COMMAND ${Python_EXECUTABLE}
            ${CMAKE_CURRENT_SOURCE_DIR}/${filename}
    # directory for importing the python bindings
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/src/api/python)
    set_tests_properties(${test_name} 
      PROPERTIES LABELS "api"
      ENVIRONMENT PYTHONPATH=${PYTHON_MODULE_PATH}:${CMAKE_SOURCE_DIR}/api/python)
endmacro()

# add specific test files
cvc5_add_python_api_test(pyapi_boilerplate boilerplate.py)
if(USE_COCOA)
  cvc5_add_python_api_test(pyapi_finite_field finite_field.py)
endif()
cvc5_add_python_api_test(pyapi_issue4889 issue4889.py)
cvc5_add_python_api_test(pyapi_issue5074 issue5074.py)
cvc5_add_python_api_test(pyapi_issue6111 issue6111.py)
cvc5_add_python_api_test(pyapi_proj-issue306 proj-issue306.py)
cvc5_add_python_api_test(pyapi_reset_assertions reset_assertions.py)
cvc5_add_python_api_test(pyapi_sep_log_api sep_log_api.py)
cvc5_add_python_api_test(pyapi_two_solvers two_solvers.py)
