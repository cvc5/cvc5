###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Mudathir Mohamed, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

cmake_minimum_required(VERSION 3.4)

project(cvc5-examples)

set(CMAKE_CXX_STANDARD 17)

enable_testing()

# Find cvc5 package. If cvc5 is not installed into the default system location
# use `cmake .. -DCMAKE_PREFIX_PATH=path/to/lib/cmake` to specify the location
# of cvc5Config.cmake.
find_package(cvc5)

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
macro(cvc5_add_example name src_files output_dir)
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
  target_link_libraries(${name} cvc5::cvc5 cvc5::cvc5parser)

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

cvc5_add_example(simple_vc_cxx "" "")
cvc5_add_example(simple_vc_quant_cxx "" "")

add_subdirectory(api/cpp)

if(TARGET cvc5::cvc5jar)
  find_package(Java REQUIRED)
  include(UseJava)

  # get directory build/install/lib where libcvc5jni.so is installed
  get_target_property(CVC5_LIB_FILE cvc5::cvc5 LOCATION)
  get_filename_component(CVC5_JNI_PATH ${CVC5_LIB_FILE} DIRECTORY)
  message(STATUS "CVC5_JNI_PATH: ${CVC5_JNI_PATH}")


  get_target_property(CVC5_JAR cvc5::cvc5jar JAR_FILE)
  message(STATUS "cvc5jar: ${CVC5_JAR}")

  add_jar(SimpleVC SimpleVC.java INCLUDE_JARS "${CVC5_JAR}")
  add_test(
    NAME java/SimpleVC
    COMMAND
      ${Java_JAVA_EXECUTABLE}
        -cp "${CVC5_JAR}:${CMAKE_BINARY_DIR}/SimpleVC.jar"
        -Djava.library.path=${CVC5_JNI_PATH}
        SimpleVC
  )
  add_subdirectory(api/java)
endif()

if(CVC5_BINDINGS_PYTHON)
  message(STATUS "with Python examples")
  # If legacy Python API has been built
  add_subdirectory(api/python)
endif()
