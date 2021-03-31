#####################
## FindJunit5.cmake
## Top contributors (to current version):
##   Mathias Preiner, Mudathir
## This file is part of the CVC4 project.
## Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
# Find Junit5
# Junit5_FOUND - should always be true for testing
# Junit5_COMMAND - command line to run junit tests

include(deps-helper)

find_jar(Junit5_JAR junit-platform-console-standalone-1.7.1.jar)

set(Junit5_FOUND_SYSTEM FALSE)
if(Junit5_JAR)
  set(Junit5_FOUND_SYSTEM TRUE)
endif()

if(NOT Junit5_FOUND_SYSTEM)
  include(ExternalProject)

  # Download junit generator jar
  ExternalProject_Add(
    Junit5
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

  set(Junit5_JAR "${DEPS_BASE}/share/java/junit-platform-console-standalone-1.7.1.jar")
endif()

set(Junit5_FOUND TRUE)

mark_as_advanced(Junit5_JAR)
mark_as_advanced(Junit5_FOUND)
mark_as_advanced(Junit5_FOUND_SYSTEM)


message(STATUS "Junit5_JAR: ${Junit5_JAR}")

#  java -jar junit-platform-console-standalone-1.7.1.jar -cp /home/mudathir/Desktop/CVC4/mudathir/test/unit/api/java:/home/mudathir/Desktop/CVC4/mudathir/build/src/api/java/cvc-1.9.0.jar -select-package cvc