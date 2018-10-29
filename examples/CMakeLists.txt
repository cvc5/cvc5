include_directories(${PROJECT_SOURCE_DIR}/src)
include_directories(${PROJECT_SOURCE_DIR}/src/include)
include_directories(${CMAKE_BINARY_DIR}/src)

# Some of the examples require boost. Enable these examples if boost is
# installed.
find_package(Boost)

set(EXAMPLES_BIN_DIR ${CMAKE_BINARY_DIR}/bin/examples)

# Create target examples.
#
# Only builds the examples, but does not run them. To run and build all
# examples, use target runexamples (below).
# Use macro cvc4_add_example to add examples.
add_custom_target(examples)

# Create target runexamples.
# Builds and runs all examples.
add_custom_target(runexamples
  COMMAND ctest --output-on-failure -L "example" -j${NTHREADS} $(ARGS)
  DEPENDS examples)

# Add example target and create test to run example with ctest.
#
# > name: The name of the example
# > src_files: The list of source files passed as string "src1 src2 ..."
#              (alternative: "src1;src2;...").  If empty, <name>.cpp is assumed.
# > libs: The list of libraries to link the example against, passed as either
#           - a list variable: set(<list name> <libs1> <libs2> ...) and pass
#                              as "${<list name>}"
#           - a string: pass as "lib1 lib2 ..." (alternative: "lib1;lib2;...")
# > output_dir: Determines the examples subdirectory and is empty (passed as
#               empty string) for the examples root directory (this)
# > ARGN: Any additional arguments passed to the macro are interpreted as
#         as arguments to the test executable.
macro(cvc4_add_example name src_files libs output_dir)
  # The build target is created without the path prefix (not supported),
  # e.g., for '<output_dir>/myexample.cpp'
  #   we create build target 'myexample'
  #   and build it with 'make myexample'.
  # As a consequence, all build target names must be globally unique.
  if("${src_files}" STREQUAL "")
    set(src_files_list ${name}.cpp)
  else()
    string(REPLACE " " ";" src_files_list "${src_files}")
  endif()
  add_executable(${name} EXCLUDE_FROM_ALL ${src_files_list})
  string(REPLACE " " ";" libs_list "${libs_list}")
  target_link_libraries(${name} ${libs})
  add_dependencies(examples ${name})
  # The test target is prefixed with test identifier 'example/' and the path,
  # e.g., for '<output_dir>/myexample.cpp'
  #   we create test target 'example/<output_dir>/myexample'
  #   and run it with 'ctest -R "example/<output_dir>/myunittest"'.
  set(example_bin_dir ${EXAMPLES_BIN_DIR}/${output_dir})
  if("${output_dir}" STREQUAL "")
    set(example_test example/${name})
  else()
    set(example_test example/${output_dir}/${name})
  endif()
  set_target_properties(${name}
    PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${example_bin_dir})
  add_test(${example_test} ${example_bin_dir}/${name} ${ARGN})
  set_tests_properties(${example_test} PROPERTIES LABELS "example")
endmacro()

set(EXAMPLES_LINK_LIBS cvc4 cvc4parser)
cvc4_add_example(simple_vc_cxx "" "${EXAMPLES_LINK_LIBS}" "")
cvc4_add_example(simple_vc_quant_cxx "" "${EXAMPLES_LINK_LIBS}" "")
cvc4_add_example(translator "" "${EXAMPLES_LINK_LIBS}" ""
    # argument to binary (for testing)
    ${CMAKE_CURRENT_SOURCE_DIR}/translator-example-input.smt2)

if(BUILD_BINDINGS_JAVA)
  find_package(Java REQUIRED)
  set(EXAMPLES_JAVA_CLASSPATH "${CMAKE_BINARY_DIR}/src/bindings/java/CVC4.jar")
  add_custom_target(SimpleVCjava
    COMMAND
      ${Java_JAVAC_EXECUTABLE}
        -cp ${EXAMPLES_JAVA_CLASSPATH} ${CMAKE_CURRENT_SOURCE_DIR}/SimpleVC.java
        -d ${CMAKE_BINARY_DIR}/bin/examples
    DEPENDS cvc4jar)
  add_dependencies(examples SimpleVCjava)
  add_test(
    NAME example/SimpleVCjava
    COMMAND
      ${Java_JAVA_EXECUTABLE}
        -Djava.library.path=${CMAKE_BINARY_DIR}/src/bindings/java/
        -cp "${EXAMPLES_JAVA_CLASSPATH}:${CMAKE_BINARY_DIR}/bin/examples/"
        SimpleVC
  )
  set_tests_properties(example/SimpleVCjava PROPERTIES LABELS "example")
endif()

add_subdirectory(api)
add_subdirectory(hashsmt)
add_subdirectory(nra-translate)
add_subdirectory(sets-translate)

