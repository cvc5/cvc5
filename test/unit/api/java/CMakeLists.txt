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

# run gradle check
add_custom_target(
  gradle-test
  ALL
  COMMAND
  # run gradlew tests
  ${PROJECT_SOURCE_DIR}/src/api/java/gradlew -p "$<TARGET_FILE_DIR:cvc4>/api/java" check
  COMMENT "Test java unit tests using gradlew check"
  VERBATIM
)

add_dependencies(gradle-test gradle-build)
add_dependencies(units gradle-test)