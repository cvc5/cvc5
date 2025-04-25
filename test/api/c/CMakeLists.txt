###############################################################################
# Top contributors (to current version):
#   Aina Niemetz
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

#-----------------------------------------------------------------------------#
# Add target 'capitests', builds and runs
# > api tests

add_custom_target(build-capitests)
add_dependencies(build-tests build-capitests)

# Disabled temporarily due to problems in the nightly builds
# # See the comment about 'make test' in test/regress/cli/CMakeLists.txt
# add_test(build_capitests_test "${CMAKE_COMMAND}" --build "${CMAKE_BINARY_DIR}" --config "$<CONFIG>" --target build-capitests)
# set_tests_properties(build_capitests_test PROPERTIES FIXTURES_SETUP build_capitests_fixture)

add_custom_target(capitests
  COMMAND ctest --output-on-failure -L "api" -j${CTEST_NTHREADS} $$ARGS
  DEPENDS build-capitests)

set(CVC5_API_TEST_FLAGS -D__BUILDING_CVC5_API_TEST -Dcvc5_obj_EXPORTS)

macro(cvc5_add_capi_test name dir)
  set(test_bin_dir ${CMAKE_BINARY_DIR}/bin/test/api/c/${dir})
  set(cname capi_${name})
  add_executable(${cname} ${name}.c)
  target_link_libraries(${cname} PUBLIC main-test)
  target_compile_definitions(${cname} PRIVATE ${CVC5_API_TEST_FLAGS})
  set_target_properties(${cname}
    PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${test_bin_dir})
  if("${dir}" STREQUAL "")
    set(testname api/c/${cname})
  else()
    set(testname api/c/${dir}/${cname})
  endif()
  add_test(${testname} ${ENV_PATH_CMD} ${test_bin_dir}/${cname})
  set_tests_properties(${testname} PROPERTIES LABELS "api capi")
  # set_tests_properties(api/cpp/${name} PROPERTIES FIXTURES_REQUIRED build_capitests_fixture)
  add_dependencies(build-capitests ${cname})
endmacro()

cvc5_add_capi_test(boilerplate "")
cvc5_add_capi_test(ouroborous "")
cvc5_add_capi_test(reset_assertions "")
cvc5_add_capi_test(sep_log_api "")
cvc5_add_capi_test(smt2_compliance "")
cvc5_add_capi_test(two_solvers "")

add_subdirectory(issues)
