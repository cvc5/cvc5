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

set(CVC4_API_TEST_FLAGS
  -D__BUILDING_CVC4_API_TEST -D__STDC_LIMIT_MACROS -D__STDC_FORMAT_MACROS)

macro(cvc4_add_api_test name)
  add_executable(${name} ${name}.cpp)
  target_link_libraries(${name} main-test)
  target_compile_definitions(${name} PRIVATE ${CVC4_API_TEST_FLAGS})
  add_test(api/${name} ${CMAKE_CURRENT_BINARY_DIR}/${name})
  set_tests_properties(api/${name} PROPERTIES LABELS "api")
  add_dependencies(build-apitests ${name})
endmacro()

cvc4_add_api_test(boilerplate)
cvc4_add_api_test(ouroborous)
cvc4_add_api_test(reset_assertions)
cvc4_add_api_test(sep_log_api)
cvc4_add_api_test(smt2_compliance)
# TODO(cvc4-projects#209): Add methods for retrieving statistics to new API
# cvc4_add_api_test(statistics)
cvc4_add_api_test(two_solvers)
cvc4_add_api_test(issue5074)
cvc4_add_api_test(issue4889)

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
