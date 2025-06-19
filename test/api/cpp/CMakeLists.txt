###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Vinícius Camillo, Andrew Reynolds
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

include_directories(${PROJECT_SOURCE_DIR}/src)
include_directories(${PROJECT_SOURCE_DIR}/src/include)

#-----------------------------------------------------------------------------#
# Add target 'apitests', builds and runs
# > api tests

add_custom_target(build-apitests)
add_dependencies(build-tests build-apitests)

# Disabled temporarily due to problems in the nightly builds
# # See the comment about 'make test' in test/regress/cli/CMakeLists.txt
# add_test(build_apitests_test "${CMAKE_COMMAND}" --build "${CMAKE_BINARY_DIR}" --config "$<CONFIG>" --target build-apitests)
# set_tests_properties(build_apitests_test PROPERTIES FIXTURES_SETUP build_apitests_fixture)

add_custom_target(apitests
  COMMAND ctest --output-on-failure -L "api" -j${CTEST_NTHREADS} $$ARGS
  DEPENDS build-apitests)

set(CVC5_API_TEST_FLAGS -D__BUILDING_CVC5_API_TEST -Dcvc5_obj_EXPORTS)

macro(cvc5_add_api_test name dir)
  set(test_bin_dir ${CMAKE_BINARY_DIR}/bin/test/api/cpp/${dir})
  add_executable(${name} ${name}.cpp)
  target_link_libraries(${name} PUBLIC main-test)
  target_compile_definitions(${name} PRIVATE ${CVC5_API_TEST_FLAGS})
  set_target_properties(${name}
    PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${test_bin_dir})
  if("${dir}" STREQUAL "")
    set(test_name api/cpp/${name})
  else()
    set(test_name api/cpp/${dir}/${name})
  endif()
  add_test(${test_name} ${ENV_PATH_CMD} ${test_bin_dir}/${name})
  set_tests_properties(${test_name} PROPERTIES LABELS "api cppapi")
  # set_tests_properties(api/cpp/${name} PROPERTIES FIXTURES_REQUIRED build_apitests_fixture)
  add_dependencies(build-apitests ${name})
endmacro()

cvc5_add_api_test(boilerplate "")
cvc5_add_api_test(ouroborous "")
cvc5_add_api_test(reset_assertions "")
cvc5_add_api_test(smt2_compliance "")
cvc5_add_api_test(two_solvers "")

if (NOT ENABLE_SAFE_MODE)
  cvc5_add_api_test(sep_log_api "")
endif()

add_subdirectory(issues)
