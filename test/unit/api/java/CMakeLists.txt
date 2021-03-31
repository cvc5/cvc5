#####################
## CMakeLists.txt
## Top contributors (to current version):
##   Mudathir Mohamed
## This file is part of the CVC4 project.
## Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##

find_package(Java REQUIRED)
include(UseJava)
find_package(JUnit REQUIRED)

# specify source files for junit tests
set(java_test_src_files
  ${CMAKE_CURRENT_SOURCE_DIR}/cvc/SolverTest.java
)

# build junit tests
add_custom_target(
  build-junit-tests
  ALL
  COMMAND
    ${Java_JAVAC_EXECUTABLE} ${java_test_src_files}
    -cp ${JUnit5_JAR}:${CVC_JAR} # add JUnit5 and cvc jar files to the class path
    -d . # specify the output directory for the generated .class files
  COMMENT "Build junit tests"
  VERBATIM
)

# make sure cvc.jar file is built first
add_dependencies(build-junit-tests cvcjar)

# run junit tests
add_custom_target(
  run-junit-tests
  ALL
  COMMAND
    # run junit tests
    ${Java_JAVA_EXECUTABLE}
    -Djava.library.path=${CVC_JNI_PATH}
    -jar ${JUnit5_JAR}
    -cp ${JUnit5_JAR}:${CVC_JAR}:.
    -select-package cvc
  COMMENT "Run junit tests"
  VERBATIM
)

add_dependencies(run-junit-tests build-junit-tests)
add_dependencies(units run-junit-tests)