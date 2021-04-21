###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Andrew V. Jones, Gereon Kremer
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

include_directories(.)
include_directories(${PROJECT_SOURCE_DIR}/src)
include_directories(${PROJECT_SOURCE_DIR}/src/include)
include_directories(${CMAKE_BINARY_DIR}/src)

#-----------------------------------------------------------------------------#
# Add target 'apitests', builds and runs
# > api tests

add_custom_target(build-apitests)
add_dependencies(build-tests build-apitests)

add_custom_target(apitests
  COMMAND ctest --output-on-failure -L "api" -j${CTEST_NTHREADS} $$ARGS
  DEPENDS build-apitests)

set(CVC5_API_TEST_FLAGS -D__BUILDING_CVC5_API_TEST)

macro(cvc5_add_api_test name)
  set(test_bin_dir ${CMAKE_BINARY_DIR}/bin/test/api/)
  add_executable(${name} ${name}.cpp)
  target_link_libraries(${name} PUBLIC main-test)
  target_compile_definitions(${name} PRIVATE ${CVC5_API_TEST_FLAGS})
  set_target_properties(${name}
    PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${test_bin_dir})
  add_test(api/${name} ${test_bin_dir}/${name})
  set_tests_properties(api/${name} PROPERTIES LABELS "api")
  add_dependencies(build-apitests ${name})
endmacro()

cvc5_add_api_test(boilerplate)
cvc5_add_api_test(ouroborous)
cvc5_add_api_test(reset_assertions)
cvc5_add_api_test(sep_log_api)
cvc5_add_api_test(smt2_compliance)
cvc5_add_api_test(two_solvers)
cvc5_add_api_test(issue5074)
cvc5_add_api_test(issue4889)

# if we've built using libedit, then we want the interactive shell tests
if (USE_EDITLINE)

  # Check for pexpect -- zero return code is success
  execute_process(
    COMMAND ${PYTHON_EXECUTABLE} -c "import pexpect"
    RESULT_VARIABLE PEXPECT_RC
    ERROR_QUIET
  )

  # Add the test if we have pexpect
  if(PEXPECT_RC EQUAL 0)
    add_test(
      NAME interactive_shell
      COMMAND
      "${PYTHON_EXECUTABLE}" "${CMAKE_SOURCE_DIR}/test/api/interactive_shell.py"
      WORKING_DIRECTORY "${CMAKE_BINARY_DIR}"
    )
  endif()
endif()


# add Python bindings tests if building with Python bindings
if (BUILD_BINDINGS_PYTHON)
  add_subdirectory(python)
endif()
