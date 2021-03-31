#####################
## FindJUnit5.cmake
## Top contributors (to current version):
##   Mathias Preiner, Mudathir
## This file is part of the CVC4 project.
## Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
# Find JUnit5
# JUnit5_FOUND - should be true for testing
# JUnit5_JAR   - absolute path to JUnit5 jar file

include(deps-helper)

find_jar(JUnit5_JAR junit-platform-console-standalone-1.7.1.jar)

set(JUnit5_FOUND_SYSTEM FALSE)
if(JUnit5_JAR)
  set(JUnit5_FOUND_SYSTEM TRUE)
endif()

if(NOT JUnit5_FOUND_SYSTEM)
  include(ExternalProject)

  # Download junit generator jar
  ExternalProject_Add(
    JUnit5
    PREFIX ${DEPS_PREFIX}
    URL https://repo1.maven.org/maven2/org/junit/platform/junit-platform-console-standalone/1.7.1/junit-platform-console-standalone-1.7.1.jar
    URL_HASH SHA1=99245bde65d028a8b8ff604be26e929ab6ff2e58
    DOWNLOAD_NO_EXTRACT ON
    CONFIGURE_COMMAND ""
    BUILD_COMMAND ""
    INSTALL_COMMAND ${CMAKE_COMMAND} -E copy
    <SOURCE_DIR>/../junit-platform-console-standalone-1.7.1.jar
    <INSTALL_DIR>/share/java/junit-platform-console-standalone-1.7.1.jar
    BUILD_BYPRODUCTS <INSTALL_DIR>/share/java/junit-platform-console-standalone-1.7.1.jar
  )

  set(JUnit5_JAR "${DEPS_BASE}/share/java/junit-platform-console-standalone-1.7.1.jar")
endif()

set(JUnit5_FOUND TRUE)

mark_as_advanced(JUnit5_JAR)
mark_as_advanced(JUnit5_FOUND)

if(JUnit5_FOUND_SYSTEM)
  message(STATUS "Found JUnit5: ${JUnit5_INCLUDE_DIR}")
else()
  message(STATUS "Building JUnit5: ${JUnit5_INCLUDE_DIR}")
endif()