###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Vinícius Camillo
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

if(WIN32)
  set(CVC5_PYAPI_TEST_DIR ${CMAKE_BINARY_DIR}/cvc5-pyapi-test)
  if(NOT EXISTS ${CVC5_PYAPI_TEST_DIR})
    set(WHEEL_INSTALL_CMD
      "${Python_EXECUTABLE} -m pip install --prefix ${CVC5_PYAPI_TEST_DIR}")

    # Build Python wheel and install it in ${CVC5_PYAPI_TEST_DIR}
    execute_process(COMMAND ${CMAKE_COMMAND}
      -DPython_EXECUTABLE=${Python_EXECUTABLE}
      -DRepairwheel_EXECUTABLE=${Repairwheel_EXECUTABLE}
      -DINSTALL_CMD="${WHEEL_INSTALL_CMD}"
      -P ${CMAKE_SOURCE_DIR}/cmake/install_python_wheel.cmake)

    execute_process(COMMAND
      ${Python_EXECUTABLE} -c
        "import os.path;import sysconfig;\
        print('${CVC5_PYAPI_TEST_DIR}'+\
        sysconfig.get_paths()['platlib'].split(sysconfig.get_config_var('platbase'))[1])"
      OUTPUT_VARIABLE PYTHON_MODULE_PATH
      OUTPUT_STRIP_TRAILING_WHITESPACE)
  endif()
else()
  set(PYTHON_MODULE_PATH ${CMAKE_BINARY_DIR}/src/api/python)
endif()

# Add Python bindings API tests.
macro(cvc5_add_python_api_test name filename)
# We create test target 'api/python/myapitest' and run it with
# 'ctest -R "api/python/myapitest"'.
  set(test_name api/python/${name})
  add_test (NAME ${test_name}
    COMMAND ${Python_EXECUTABLE}
            ${CMAKE_CURRENT_SOURCE_DIR}/${filename})
    # directory for importing the python bindings
    set_tests_properties(${test_name}
      PROPERTIES LABELS "api"
      ENVIRONMENT PYTHONPATH=${PYTHON_MODULE_PATH})
endmacro()

# add specific test files
cvc5_add_python_api_test(pyapi_boilerplate boilerplate.py)
cvc5_add_python_api_test(pyapi_issue4889 issue4889.py)
cvc5_add_python_api_test(pyapi_issue5074 issue5074.py)
cvc5_add_python_api_test(pyapi_issue6111 issue6111.py)
cvc5_add_python_api_test(pyapi_proj-issue306 proj-issue306.py)
cvc5_add_python_api_test(pyapi_reset_assertions reset_assertions.py)
cvc5_add_python_api_test(pyapi_sep_log_api sep_log_api.py)
cvc5_add_python_api_test(pyapi_two_solvers two_solvers.py)
