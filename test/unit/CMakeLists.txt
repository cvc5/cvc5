include_directories(.)
include_directories(${PROJECT_SOURCE_DIR}/src)
include_directories(${PROJECT_SOURCE_DIR}/src/include)
include_directories(${CMAKE_BINARY_DIR}/src)

#-----------------------------------------------------------------------------#
# Add target 'units', builds and runs
# > unit tests

add_custom_target(units
  COMMAND ctest --output-on-failure -L "unit" -j${NTHREADS} $(ARGS))

set(CVC4_CXXTEST_FLAGS_BLACK
  -D__BUILDING_CVC4LIB_UNIT_TEST -D__BUILDING_CVC4PARSERLIB_UNIT_TEST
  -D__STDC_LIMIT_MACROS -D__STDC_FORMAT_MACROS)
set(CVC4_CXXTEST_FLAGS_WHITE -fno-access-control ${CVC4_CXXTEST_FLAGS_BLACK})

macro(cvc4_add_unit_test is_white name)
  # cxxtest_add_test generates the unit test executables into directory
  # CMAKE_BINARY_DIR/test/unit by default and does not allow to change this
  # location (it's possible to set corresponding target properties with
  # set_target_properties, but then the test environment does not find them).
  # Hence, these are the only executables that are not generated into our
  # default directory for executables (CMAKE_BINARY_DIR/bin).
  cxxtest_add_test(${name} ${name}.cpp ${CMAKE_CURRENT_LIST_DIR}/${name}.h)
  set_tests_properties(${name} PROPERTIES LABELS "unit")
  target_link_libraries(${name} main-test)
  target_compile_definitions(${name} PRIVATE ${CVC4_CXXTEST_FLAGS_BLACK})
  if(${is_white})
    target_compile_options(${name} PRIVATE -fno-access-control)
  endif()
  # Disable the Wsuggest-override warnings for the unit tests. CxxTest generates
  # code that does not properly add the override keyword to runTest().
  target_compile_options(${name} PRIVATE -Wno-suggest-override)
  add_dependencies(units ${name})
  if(ENABLE_COVERAGE)
    add_dependencies(coverage ${name})
  endif()
endmacro()

macro(cvc4_add_unit_test_black name)
  cvc4_add_unit_test(FALSE ${name})
endmacro()
macro(cvc4_add_unit_test_white name)
  cvc4_add_unit_test(TRUE ${name})
endmacro()

add_subdirectory(base)
add_subdirectory(context)
add_subdirectory(expr)
add_subdirectory(main)
add_subdirectory(parser)
add_subdirectory(prop)
add_subdirectory(theory)
add_subdirectory(util)
