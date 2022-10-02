###############################################################################
# Top contributors (to current version):
#   Mudathir Mohamed, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find JUnit
# JUnit_FOUND - should be true for testing
# JUnit_JAR   - absolute path to JUnit5 jar file
##

include(deps-helper)

find_jar(JUnit_JAR junit-platform-console-standalone
  PATHS
    ${DEPS_BASE}/share/java
    $ENV{PATH} $ENV{HOME} $ENV{CLASSPATH} $ENV{JUNIT_HOME}
)

set(JUnit_FOUND_SYSTEM FALSE)
if(JUnit_JAR)
  set(JUnit_FOUND_SYSTEM TRUE)
endif()

if(NOT JUnit_FOUND_SYSTEM)
  check_auto_download("JUnit" "")
  set(JUNIT_VERSION 1.7.1)
  include(ExternalProject)

  # Download junit generator jar
  ExternalProject_Add(
    JUnit-EP-jar
    PREFIX ${DEPS_PREFIX}
    URL https://repo1.maven.org/maven2/org/junit/platform/junit-platform-console-standalone/${JUNIT_VERSION}/junit-platform-console-standalone-${JUNIT_VERSION}.jar
    URL_HASH SHA1=99245bde65d028a8b8ff604be26e929ab6ff2e58
    DOWNLOAD_NO_EXTRACT ON
    CONFIGURE_COMMAND ""
    BUILD_COMMAND ""
    INSTALL_COMMAND ${CMAKE_COMMAND} -E copy
      <SOURCE_DIR>/../junit-platform-console-standalone-${JUNIT_VERSION}.jar
      <INSTALL_DIR>/share/java/junit-platform-console-standalone-${JUNIT_VERSION}.jar
    BUILD_BYPRODUCTS <INSTALL_DIR>/share/java/junit-platform-console-standalone-${JUNIT_VERSION}.jar
  )

  set(JUnit_JAR "${DEPS_BASE}/share/java/junit-platform-console-standalone-${JUNIT_VERSION}.jar")
endif()

set(JUnit_FOUND TRUE)

mark_as_advanced(JUnit_JAR)
mark_as_advanced(JUnit_FOUND)

if(JUnit_FOUND_SYSTEM)
  message(STATUS "Found JUnit: ${JUnit_JAR}")
else()
  message(STATUS "Downloading JUnit: ${JUnit_JAR}")
endif()