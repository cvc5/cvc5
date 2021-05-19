###############################################################################
# Top contributors (to current version):
#   Mudathir Mohamed
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

find_package(Java REQUIRED)
include(UseJava)
find_package(JUnit REQUIRED)

# specify source files for junit tests
set(java_test_src_files
  ${CMAKE_CURRENT_SOURCE_DIR}/cvc5/SolverTest.java
)

# build junit tests
add_custom_target(
  build-junit-tests
  ALL
  COMMAND
    ${Java_JAVAC_EXECUTABLE} ${java_test_src_files}
    -cp ${JUnit_JAR}:${CVC5_JAR_PATH} # add JUnit and cvc5 jar files to the class path
    -d . # specify the output directory for the generated .class files
  COMMENT "Build junit tests"
  VERBATIM
)

# make sure junit jar file is present
add_dependencies(build-junit-tests JUnit-EP-jar)
# make sure cvc.jar file is built first
add_dependencies(build-junit-tests cvc5jar)

get_filename_component(CVC5_JNI_PATH ${CVC5_JAR_PATH} DIRECTORY)

# run junit tests
add_custom_target(
  run-junit-tests
  ALL
  COMMAND
    # run junit tests
    ${Java_JAVA_EXECUTABLE}
    -Djava.library.path=${CVC5_JNI_PATH}
    -jar ${JUnit_JAR}
    -cp ${JUnit_JAR}:${CVC5_JAR_PATH}:.
    -select-package cvc5
  COMMENT "Run junit tests"
  VERBATIM
)

add_dependencies(run-junit-tests build-junit-tests)
add_dependencies(units run-junit-tests)