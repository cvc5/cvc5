###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Andrew Reynolds, Mathias Preiner
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

include_directories(.)
include_directories(${PROJECT_SOURCE_DIR}/src)
include_directories(${PROJECT_SOURCE_DIR}/src/include)
include_directories(${CMAKE_BINARY_DIR}/src)

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

macro(cvc5_add_api_test name)
  set(test_bin_dir ${CMAKE_BINARY_DIR}/bin/test/api/c)
  add_executable(${name} ${name}.cpp)
  target_link_libraries(${name} PUBLIC main-test)
  target_compile_definitions(${name} PRIVATE ${CVC5_API_TEST_FLAGS})
  set_target_properties(${name}
    PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${test_bin_dir})
  add_test(api/c/${name} ${ENV_PATH_CMD} ${test_bin_dir}/${name})
  set_tests_properties(api/c/${name} PROPERTIES LABELS "api")
  # set_tests_properties(api/c/${name} PROPERTIES FIXTURES_REQUIRED build_apitests_fixture)
  add_dependencies(build-apitests ${name})
endmacro()

cvc5_add_api_test(issue11069)
