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

  set(WHEEL_INSTALL_CMD
       "${Python_EXECUTABLE} -m pip install --prefix ${CVC5_PYAPI_TEST_DIR}")

  # Install the cvc5 Python bindings in the build directory to run tests.
  # On Windows, adding the directory with the Python bindings to PYTHONPATH
  # is not enought because Python only searches for DLL dependencies for
  # extension modules in system paths and the directory containing the PYD file.
  # Specifically, since Python 3.8, PATH and the current working directory are
  # no longer used for this purpose. See:
  #  https://docs.python.org/3/whatsnew/3.8.html#bpo-36085-whatsnew
  add_custom_command(
    OUTPUT ${CVC5_PYAPI_TEST_DIR}
    COMMAND
      ${CMAKE_COMMAND}
        -DPython_EXECUTABLE=${Python_EXECUTABLE}
        -DRepairwheel_EXECUTABLE=${Repairwheel_EXECUTABLE}
        -DBUILD_DIR=${CMAKE_BINARY_DIR}
        -DDEPS_BASE=${DEPS_BASE}
        -DINSTALL_CMD="${WHEEL_INSTALL_CMD}"
        -P ${CMAKE_SOURCE_DIR}/cmake/install_python_wheel.cmake
    DEPENDS cvc5_python_api
  )

  add_custom_target(setup-cvc5-pyapi DEPENDS ${CVC5_PYAPI_TEST_DIR})

  add_dependencies(build-tests setup-cvc5-pyapi)

  # Get path to the python bindings installed in the build directory
  execute_process(COMMAND
    ${Python_EXECUTABLE} -c
      "import os.path;import sysconfig;\
      print('${CVC5_PYAPI_TEST_DIR}'+\
      sysconfig.get_paths()['platlib'].split(sysconfig.get_config_var('platbase'))[1])"
    OUTPUT_VARIABLE PYTHON_MODULE_PATH
    OUTPUT_STRIP_TRAILING_WHITESPACE)
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
