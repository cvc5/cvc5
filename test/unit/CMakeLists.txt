include_directories(.)
include_directories(${PROJECT_SOURCE_DIR}/src)
include_directories(${PROJECT_SOURCE_DIR}/src/include)
include_directories(${CMAKE_BINARY_DIR}/src)

set(CVC4_CXXTEST_FLAGS_BLACK
  -D__BUILDING_CVC4LIB_UNIT_TEST -D__BUILDING_CVC4PARSERLIB_UNIT_TEST
	-D__STDC_LIMIT_MACROS -D__STDC_FORMAT_MACROS)
set(CVC4_CXXTEST_FLAGS_WHITE -fno-access-control ${CVC4_CXXTEST_FLAGS_BLACK})

macro(cvc4_add_unit_test is_white name)
  cxxtest_add_test(${name} ${name}.cpp ${CMAKE_CURRENT_LIST_DIR}/${name}.h)
  set_tests_properties(${name} PROPERTIES LABELS "unit")
  target_link_libraries(${name} main)
  target_compile_definitions(${name} PRIVATE ${CVC4_CXXTEST_FLAGS_BLACK})
  if(${is_white})
    target_compile_options(${name} PRIVATE -fno-access-control)
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

add_custom_target(units COMMAND ctest -L "unit")
