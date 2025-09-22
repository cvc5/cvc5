###############################################################################
# Top contributors (to current version):
#   Daniel Larraz
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

find_package(Java REQUIRED)
include(UseJava)

get_target_property(CVC5_JAR_PATH cvc5jar JAR_FILE)
get_filename_component(CVC5_JNI_PATH ${CVC5_JAR_PATH} DIRECTORY)

add_custom_target(build-japitests)
add_dependencies(build-apitests build-japitests)

add_custom_target(japitests
  COMMAND ctest --output-on-failure -L "japi" -j${CTEST_NTHREADS} $$ARGS
  DEPENDS build-japitests)

macro(cvc5_add_java_api_test name dir)
  set(test_bin_dir ${CMAKE_BINARY_DIR}/bin/test/api/java/${dir})
  add_jar(${name}
    SOURCES ${name}.java
    INCLUDE_JARS ${CVC5_JAR_PATH}
    ENTRY_POINT ${name}
    OUTPUT_DIR ${test_bin_dir}
  )
  if("${dir}" STREQUAL "")
    set(testname api/java/${name})
  else()
    set(testname api/java/${dir}/${name})
  endif()
  add_test(${testname}
      ${Java_JAVA_EXECUTABLE}
        -Djava.library.path=${CVC5_JNI_PATH}
        -cp "${CVC5_JAR_PATH}:${test_bin_dir}/${name}.jar" ${name}
    )
  set_tests_properties(${testname} PROPERTIES LABELS "api japi")
  add_dependencies(build-japitests ${name})
endmacro()

# TODO: Set Java API test infrastructure for Windows (see issue #12143)
if(NOT WIN32)

  add_subdirectory(issues)

endif()