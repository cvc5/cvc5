###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Mathias Preiner, Gereon Kremer
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

find_package(GTest REQUIRED)
include(GoogleTest)

include_directories(.)
include_directories(${PROJECT_SOURCE_DIR}/src)
include_directories(${PROJECT_SOURCE_DIR}/src/include)
include_directories(${CMAKE_BINARY_DIR}/src)

#-----------------------------------------------------------------------------#
# Add target 'units', builds and runs
# > unit tests

add_custom_target(build-units)
add_dependencies(build-tests build-units)

add_custom_target(units
  COMMAND ctest --output-on-failure -L "unit" -j${CTEST_NTHREADS} $$ARGS
  DEPENDS build-units)

set(CVC5_UNIT_TEST_FLAGS_BLACK
  -D__BUILDING_CVC5LIB_UNIT_TEST -D__BUILDING_CVC5PARSERLIB_UNIT_TEST)

# Generate and add unit test.
macro(cvc5_add_unit_test is_white name output_dir)
  set(test_src ${CMAKE_CURRENT_LIST_DIR}/${name}.cpp)
  add_executable(${name} ${test_src})
  target_compile_definitions(${name} PRIVATE ${CVC5_UNIT_TEST_FLAGS_BLACK})
  gtest_add_tests(TARGET ${name})
  target_link_libraries(${name} PUBLIC main-test)
  target_link_libraries(${name} PUBLIC GTest::Main)
  target_link_libraries(${name} PUBLIC GTest::GTest)

  if(USE_CLN)
    target_link_libraries(${name} PUBLIC CLN)
  endif()
  if(USE_POLY)
    target_link_libraries(${name} PUBLIC Polyxx)
  endif()
  target_link_libraries(${name} PUBLIC GMP)
  if(${is_white})
    target_compile_options(${name} PRIVATE -fno-access-control)
  endif()
  # Disable the Wunused-comparison warnings for the unit tests.
  check_cxx_compiler_flag("-Wno-unused-comparison" HAVE_FLAGWno_unused_comparison)
  if(HAVE_FLAGWno_unused_comparison)
    target_compile_options(${name} PRIVATE -Wno-unused-comparison)
  endif()
  add_dependencies(build-units ${name})
  # Generate into bin/test/unit/<output_dir>.
  set(test_bin_dir ${CMAKE_BINARY_DIR}/bin/test/unit/${output_dir})
  set_target_properties(${name}
    PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${test_bin_dir})
  # The test target is prefixed with test identifier 'unit/' and the path,
  # e.g., for '<output_dir>/myunittest.h'
  #   we create test target 'unit/<output_dir>/myunittest'
  #   and run it with 'ctest -R "example/<output_dir>/myunittest"'.
  if("${output_dir}" STREQUAL "")
    set(test_name unit/${name})
  else()
    set(test_name unit/${output_dir}/${name})
  endif()
  add_test(${test_name} ${test_bin_dir}/${name})
  set_tests_properties(${test_name} PROPERTIES LABELS "unit")
endmacro()

macro(cvc5_add_unit_test_black name output_dir)
  cvc5_add_unit_test(FALSE ${name} ${output_dir})
endmacro()
macro(cvc5_add_unit_test_white name output_dir)
  cvc5_add_unit_test(TRUE ${name} ${output_dir})
endmacro()

add_subdirectory(api)
add_subdirectory(base)
add_subdirectory(context)
add_subdirectory(node)
add_subdirectory(main)
add_subdirectory(parser)
add_subdirectory(printer)
add_subdirectory(prop)
add_subdirectory(theory)
add_subdirectory(preprocessing)
add_subdirectory(util)
