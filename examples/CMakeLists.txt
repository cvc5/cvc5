cmake_minimum_required(VERSION 3.4)

project(cvc4-examples)

set(CMAKE_CXX_STANDARD 11)

enable_testing()

# Find CVC4 package. If CVC4 is not installed into the default system location
# use `cmake .. -DCMAKE_PREFIX_PATH=path/to/lib/cmake` to specify the location
# of CVC4Config.cmake.
find_package(CVC4)

# Some of the examples require boost. Enable these examples if boost is
# installed.
find_package(Boost 1.50.0)

set(EXAMPLES_BIN_DIR ${CMAKE_BINARY_DIR}/bin)

# Add example target and create test to run example with ctest.
#
# > name: The name of the example
# > src_files: The list of source files passed as string "src1 src2 ..."
#              (alternative: "src1;src2;...").  If empty, <name>.cpp is assumed.
# > output_dir: Determines the examples subdirectory and is empty (passed as
#               empty string) for the examples root directory (this)
# > ARGN: Any additional arguments passed to the macro are interpreted as
#         as arguments to the test executable.
macro(cvc4_add_example name src_files output_dir)
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

  add_executable(${name} ${src_files_list})
  target_link_libraries(${name} CVC4::cvc4 CVC4::cvc4parser)

  # The test target is prefixed with the path,
  # e.g., for '<output_dir>/myexample.cpp'
  #   we create test target '<output_dir>/myexample'
  #   and run it with 'ctest -R "<output_dir>/myexample"'.
  set(example_bin_dir ${EXAMPLES_BIN_DIR}/${output_dir})
  if("${output_dir}" STREQUAL "")
    set(example_test ${name})
  else()
    set(example_test ${output_dir}/${name})
  endif()
  set_target_properties(${name}
    PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${example_bin_dir})
  add_test(${example_test} ${example_bin_dir}/${name} ${ARGN})
endmacro()

cvc4_add_example(simple_vc_cxx "" "")
cvc4_add_example(simple_vc_quant_cxx "" "")
# TODO(project issue $206): Port example to new API
# cvc4_add_example(translator "" ""
#     # argument to binary (for testing)
#     ${CMAKE_CURRENT_SOURCE_DIR}/translator-example-input.smt2)

add_subdirectory(api)
# TODO(project issue $206): Port example to new API
# add_subdirectory(hashsmt)
# add_subdirectory(nra-translate)
# add_subdirectory(sets-translate)

if(TARGET CVC4::cvc4jar)
  find_package(Java REQUIRED)
  include(UseJava)

  ## disabled until bindings for the new API are in place (issue #2284)
  # get_target_property(CVC4_JAR CVC4::cvc4jar JAR_FILE)
  #
  # add_jar(SimpleVC SimpleVC.java INCLUDE_JARS "${CVC4_JAR}")
  #
  # add_test(
  #   NAME java/SimpleVC
  #   COMMAND
  #     ${Java_JAVA_EXECUTABLE}
  #       -cp "${CVC4_JAR}:${CMAKE_BINARY_DIR}/SimpleVC.jar"
  #       -Djava.library.path=${CVC4_JNI_PATH}
  #       SimpleVC
  # )

  add_subdirectory(api/java)
endif()

if(CVC4_BINDINGS_PYTHON)
  # If legacy Python API has been built
  add_subdirectory(api/python)
endif()
