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


# run junit tests
add_custom_target(
  junit-tests
  ALL
  COMMAND
    # run junit tests
    ${Java_JAVA_EXECUTABLE} -jar ${Junit5_JAR}
    -cp ${PROJECT_SOURCE_DIR}/test/unit/api/java
    #-cp $<TARGET_FILE:cvcjar>
    -cp ${CVC_JAR}
    -select-package cvc
  COMMENT "Run junit tests"
  VERBATIM
)

add_dependencies(junit-tests cvcjar)
add_dependencies(units junit-tests)