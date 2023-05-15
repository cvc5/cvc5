###############################################################################
# Top contributors (to current version):
#   Mudathir Mohamed, Gereon Kremer, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

find_package(Java REQUIRED)
include(UseJava)
find_package(JUnit REQUIRED)

get_target_property(CVC5_JAR_PATH cvc5jar JAR_FILE)
get_filename_component(CVC5_JNI_PATH ${CVC5_JAR_PATH} DIRECTORY)

# specify source files for junit tests
set(java_test_src_files
  ${CMAKE_CURRENT_SOURCE_DIR}/DatatypeTest.java
  ${CMAKE_CURRENT_SOURCE_DIR}/FiniteFieldTest.java
  ${CMAKE_CURRENT_SOURCE_DIR}/GrammarTest.java
  ${CMAKE_CURRENT_SOURCE_DIR}/OpTest.java
  ${CMAKE_CURRENT_SOURCE_DIR}/ResultTest.java
  ${CMAKE_CURRENT_SOURCE_DIR}/SolverTest.java
  ${CMAKE_CURRENT_SOURCE_DIR}/SortTest.java
  ${CMAKE_CURRENT_SOURCE_DIR}/SynthResultTest.java
  ${CMAKE_CURRENT_SOURCE_DIR}/TermTest.java
)

# build junit tests
add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/tests/SolverTest.class
  DEPENDS JUnit-EP-jar cvc5jar ${java_test_src_files}
  COMMAND
    ${Java_JAVAC_EXECUTABLE} ${java_test_src_files}
    -cp ${JUnit_JAR}:${CVC5_JAR_PATH} # add JUnit and cvc5 jar files to the class path
    -d . # specify the output directory for the generated .class files
  COMMENT "Build junit tests"
  VERBATIM
)
add_custom_target(build-junit-tests
  DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/tests/SolverTest.class
)
add_dependencies(build-units build-junit-tests)

macro(cvc5_add_java_api_test name)
  add_test (NAME unit/api/java/${name}
    COMMAND
      ${Java_JAVA_EXECUTABLE}
      -Djava.library.path=${CVC5_JNI_PATH}
      -jar ${JUnit_JAR}
      -cp ${JUnit_JAR}:${CVC5_JAR_PATH}:.
      -select-package tests
      -n tests.${name}
  )
  set_tests_properties(unit/api/java/${name} PROPERTIES LABELS "unit java")
endmacro()

if(USE_COCOA)
  cvc5_add_java_api_test(FiniteFieldTest)
endif()
cvc5_add_java_api_test(DatatypeTest)
cvc5_add_java_api_test(GrammarTest)
cvc5_add_java_api_test(OpTest)
cvc5_add_java_api_test(ResultTest)
cvc5_add_java_api_test(SolverTest)
cvc5_add_java_api_test(SortTest)
cvc5_add_java_api_test(SynthResultTest)
cvc5_add_java_api_test(TermTest)

cvc5_add_unit_test_white(UncoveredTest api/java)
