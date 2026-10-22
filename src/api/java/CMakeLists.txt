###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

# create directories
file(MAKE_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/io/github/cvc5/api")

configure_file(genenums.py.in genenums.py)

# Generate Kind.java
set(JAVA_KIND_FILE
  "${CMAKE_CURRENT_BINARY_DIR}/io/github/cvc5/Kind.java"
)
add_custom_command(
  OUTPUT
    ${JAVA_KIND_FILE}
  COMMAND
    "${Python_EXECUTABLE}"
    "${CMAKE_CURRENT_BINARY_DIR}/genenums.py"
    --enums-header "${PROJECT_SOURCE_DIR}/include/cvc5/cvc5_kind.h"
    --java-api-path "${CMAKE_CURRENT_BINARY_DIR}/io/github/"
  DEPENDS
    "${CMAKE_CURRENT_BINARY_DIR}/genenums.py"
    "${PROJECT_SOURCE_DIR}/src/api/parseenums.py"
    "${PROJECT_SOURCE_DIR}/include/cvc5/cvc5_kind.h"
)
add_custom_target(generate-java-kinds DEPENDS ${JAVA_KIND_FILE})

# Generate ProofRule.java
set(JAVA_PROOF_RULE_FILE
  "${CMAKE_CURRENT_BINARY_DIR}/io/github/cvc5/ProofRule.java"
)
add_custom_command(
  OUTPUT
    ${JAVA_PROOF_RULE_FILE}
  COMMAND
    "${Python_EXECUTABLE}"
    "${CMAKE_CURRENT_BINARY_DIR}/genenums.py"
    --enums-header "${PROJECT_SOURCE_DIR}/include/cvc5/cvc5_proof_rule.h"
    --java-api-path "${CMAKE_CURRENT_BINARY_DIR}/io/github/"
  DEPENDS
    "${CMAKE_CURRENT_BINARY_DIR}/genenums.py"
    "${PROJECT_SOURCE_DIR}/src/api/parseenums.py"
    "${PROJECT_SOURCE_DIR}/include/cvc5/cvc5_proof_rule.h"
)
add_custom_target(generate-java-proofrules DEPENDS ${JAVA_PROOF_RULE_FILE})

# Generate SkolemId.java
set(JAVA_SKOLEM_FUN_ID_FILE
  "${CMAKE_CURRENT_BINARY_DIR}/io/github/cvc5/SkolemId.java"
)
add_custom_command(
  OUTPUT
    ${JAVA_SKOLEM_FUN_ID_FILE}
  COMMAND
    "${Python_EXECUTABLE}"
    "${CMAKE_CURRENT_BINARY_DIR}/genenums.py"
    --enums-header "${PROJECT_SOURCE_DIR}/include/cvc5/cvc5_skolem_id.h"
    --java-api-path "${CMAKE_CURRENT_BINARY_DIR}/io/github/"
  DEPENDS
    "${CMAKE_CURRENT_BINARY_DIR}/genenums.py"
    "${PROJECT_SOURCE_DIR}/src/api/parseenums.py"
    "${PROJECT_SOURCE_DIR}/include/cvc5/cvc5_skolem_id.h"
)
add_custom_target(generate-java-skolemfunids DEPENDS ${JAVA_SKOLEM_FUN_ID_FILE})

set(JAVA_TYPES_FILES
  "${CMAKE_CURRENT_BINARY_DIR}/io/github/cvc5/modes/BlockModelsMode.java"
  "${CMAKE_CURRENT_BINARY_DIR}/io/github/cvc5/modes/FindSynthTarget.java"
  "${CMAKE_CURRENT_BINARY_DIR}/io/github/cvc5/modes/InputLanguage.java"
  "${CMAKE_CURRENT_BINARY_DIR}/io/github/cvc5/modes/LearnedLitType.java"
  "${CMAKE_CURRENT_BINARY_DIR}/io/github/cvc5/modes/ProofComponent.java"
  "${CMAKE_CURRENT_BINARY_DIR}/io/github/cvc5/RoundingMode.java"
  "${CMAKE_CURRENT_BINARY_DIR}/io/github/cvc5/UnknownExplanation.java"
)
add_custom_command(
  OUTPUT
  ${JAVA_TYPES_FILES}
  COMMAND
    "${Python_EXECUTABLE}"
    "${CMAKE_CURRENT_BINARY_DIR}/genenums.py"
    --enums-header "${PROJECT_SOURCE_DIR}/include/cvc5/cvc5_types.h"
    --java-api-path "${CMAKE_CURRENT_BINARY_DIR}/io/github/"
  DEPENDS
    "${CMAKE_CURRENT_BINARY_DIR}/genenums.py"
    "${PROJECT_SOURCE_DIR}/src/api/parseenums.py"
    "${PROJECT_SOURCE_DIR}/include/cvc5/cvc5_types.h"
)
add_custom_target(generate-java-types DEPENDS ${JAVA_TYPES_FILES})

# Generate CApi.java, the bindings of the cvc5 C API for the Foreign Function &
# Memory API
set(JAVA_CAPI_FILE "${CMAKE_CURRENT_BINARY_DIR}/io/github/cvc5/CApi.java")
add_custom_command(
  OUTPUT
    ${JAVA_CAPI_FILE}
  COMMAND
    "${Python_EXECUTABLE}"
    "${CMAKE_CURRENT_LIST_DIR}/genffm.py"
    --include-dir "${PROJECT_SOURCE_DIR}/include"
    --java-api-path "${CMAKE_CURRENT_BINARY_DIR}"
  DEPENDS
    "${CMAKE_CURRENT_LIST_DIR}/genffm.py"
    "${PROJECT_SOURCE_DIR}/include/cvc5/c/cvc5.h"
    "${PROJECT_SOURCE_DIR}/include/cvc5/c/cvc5_parser.h"
)
add_custom_target(generate-java-capi DEPENDS ${JAVA_CAPI_FILE})

# find java: the Foreign Function & Memory API requires Java 22, and we
# require the LTS release that follows it
find_package(Java 25 COMPONENTS Development REQUIRED)
include(UseJava)
# compile for the minimum required Java version, whatever the JDK
set(CMAKE_JAVA_COMPILE_FLAGS --release 25)

# specify java source files
set(JAVA_FILES
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/AbstractPointer.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/AbstractPlugin.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Callbacks.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Command.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Context.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/CVC5ApiException.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/CVC5ApiOptionException.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/CVC5ApiRecoverableException.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/CVC5ParserException.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Datatype.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/DatatypeConstructor.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/DatatypeConstructorDecl.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/DatatypeDecl.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/DatatypeSelector.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Grammar.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/InputParser.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/IOracle.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/IPointer.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Native.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/NativeContext.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Op.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/OptionInfo.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Pair.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Proof.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Result.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Solver.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Sort.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Stat.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Statistics.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/SymbolManager.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/SynthResult.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Term.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/TermManager.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Triplet.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Utils.java
  ${JAVA_CAPI_FILE}
  ${JAVA_KIND_FILE}
  ${JAVA_PROOF_RULE_FILE}
  ${JAVA_SKOLEM_FUN_ID_FILE}
  ${JAVA_SORT_KIND_FILE}
  ${JAVA_TYPES_FILES}
)

# Normalize the system name and CPU architecture according to the conventions of
# the os-maven-plugin, so that the native library is built under the path
# ${NATIVE_PREFIX}/${SYS_NAME}/${CPU_ARCH}. This enables the creation of
# a single JAR that can contain native libraries for multiple OSes and
# CPU architectures simultaneously.
# Additionally, it prevents file collisions when multiple JARs containing
# a native library for the same OS but different architectures are added to
# the classpath at the same time.
set(NATIVE_PREFIX "cvc5-libs")
string(TOLOWER "${CMAKE_SYSTEM_PROCESSOR}" CPU_ARCH)
# Normalize supported CPU architectures
if(CPU_ARCH MATCHES "x86_64|amd64")
  set(CPU_ARCH "x86_64")
elseif(CPU_ARCH MATCHES "aarch64|arm64")
  set(CPU_ARCH "aarch_64")
endif()
# Normalize supported system names
string(TOLOWER "${CMAKE_SYSTEM_NAME}" SYS_NAME)
if(CMAKE_SYSTEM_NAME STREQUAL "Darwin")
  set(SYS_NAME "osx")
endif()
set(NATIVE_OUTPUT_DIR "${CMAKE_CURRENT_BINARY_DIR}/${NATIVE_PREFIX}/${SYS_NAME}/${CPU_ARCH}")

if(WIN32)
  set(PATH_SEP ";")
else()
  set(PATH_SEP ":")
endif()

# The Java API calls the C API of the cvc5 libraries through the Foreign
# Function & Memory API and has no native library of its own.
if(BUILD_SHARED_LIBS)
  # It loads libcvc5 and libcvc5parser.
  set(CVC5_JAVA_LIBRARY_PATH
    "$<TARGET_FILE_DIR:cvc5>${PATH_SEP}$<TARGET_FILE_DIR:cvc5parser>")
else()
  # In a static build, it loads a self-contained shared libcvc5 instead, which
  # contains cvc5, its parser and their dependencies. It is built from the
  # objects of the static libraries, and bundled in the native JAR.
  add_library(cvc5-java-native SHARED
    $<TARGET_OBJECTS:cvc5-obj>
    $<TARGET_OBJECTS:cvc5base>
    $<TARGET_OBJECTS:cvc5context>
    $<TARGET_OBJECTS:cvc5parser-objs>
    $<TARGET_OBJECTS:cvc5parserapi-objs>
  )
  # Link the dependencies of cvc5 and its parser.
  target_link_libraries(cvc5-java-native PRIVATE cvc5parser)
  set_target_properties(cvc5-java-native PROPERTIES
    OUTPUT_NAME cvc5
    LIBRARY_OUTPUT_DIRECTORY "${NATIVE_OUTPUT_DIR}"
    RUNTIME_OUTPUT_DIRECTORY "${NATIVE_OUTPUT_DIR}"
  )
  if(WIN32)
    # Statically link all libraries, including MinGW-w64 libraries
    set_target_properties(cvc5-java-native PROPERTIES
      LINK_FLAGS -static
      LINK_SEARCH_START_STATIC ON
      LINK_SEARCH_END_STATIC ON
    )
    # Java on Windows expects native libraries without the prefix
    set_target_properties(cvc5-java-native PROPERTIES PREFIX "" IMPORT_PREFIX "")
  endif()
  set(CVC5_JAVA_LIBRARY_PATH "${NATIVE_OUTPUT_DIR}")
endif()

# Create cvc5.jar file
if (WIN32)
  # CMake creates a symbolic link pointing to the jar with
  # the version info when the VERSION attribute is provided.
  # This fails on Windows so we don't provide it.
  add_jar(cvc5jar
    SOURCES
    ${JAVA_FILES}
    OUTPUT_NAME cvc5
  )
else()
  add_jar(cvc5jar
    SOURCES
    ${JAVA_FILES}
    VERSION ${CVC5_MAVEN_VERSION}
    OUTPUT_NAME cvc5
  )
endif()

add_dependencies(cvc5jar generate-java-capi generate-java-kinds cvc5 cvc5parser)
if(TARGET cvc5-java-native)
  add_dependencies(cvc5jar cvc5-java-native)
endif()
# The library path for running the Java API from the build directory (tests)
set_target_properties(cvc5jar PROPERTIES
  CVC5_JAVA_LIBRARY_PATH "${CVC5_JAVA_LIBRARY_PATH}")

if(BUILD_DOCS)
  # Build cvc5-sources.jar to enable viewing, navigation, and debugging of the library source code
  set(SOURCES_JAR ${CMAKE_CURRENT_BINARY_DIR}/cvc5-sources.jar)

  add_custom_command(
      OUTPUT ${SOURCES_JAR}
      COMMAND ${Java_JAR_EXECUTABLE} cf ${SOURCES_JAR}
              -C ${CMAKE_CURRENT_LIST_DIR} io/github/cvc5
              -C ${CMAKE_CURRENT_BINARY_DIR} io/github/cvc5
      DEPENDS ${JAVA_FILES}
      COMMENT "Generating sources JAR"
  )
  add_custom_target(cvc5-sources-jar ALL DEPENDS ${SOURCES_JAR})
endif()

if(NOT BUILD_SHARED_LIBS)
  # Build a JAR including the native library for publication to Maven Central
  set(NATIVE_JAR ${CMAKE_CURRENT_BINARY_DIR}/cvc5-${SYS_NAME}-${CPU_ARCH}.jar)
  add_custom_command(
      OUTPUT ${NATIVE_JAR}
      COMMAND ${Java_JAR_EXECUTABLE} cf ${NATIVE_JAR} -C ${CMAKE_CURRENT_BINARY_DIR} ${NATIVE_PREFIX}
      DEPENDS cvc5-java-native
      COMMENT "Generating native JAR"
  )
  add_custom_target(cvc5-native-jar ALL DEPENDS ${NATIVE_JAR})
endif()

# POM file for publishing cvc5 Java bindings to Maven Central
configure_file(pom.xml.in ${PROJECT_BINARY_DIR}/pom.xml @ONLY)

if(NOT BUILD_SHARED_LIBS)
  # Install the self-contained libcvc5 in its own directory, so that it does
  # not take the place of the static libraries when linking against cvc5.
  install(TARGETS cvc5-java-native
    LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}/cvc5-java COMPONENT java-api
    RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}/cvc5-java COMPONENT java-api
    ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}/cvc5-java COMPONENT java-api
  )
endif()

install_jar(cvc5jar
  DESTINATION share/java
  COMPONENT java-api
)

install_jar_exports(
  TARGETS cvc5jar
  NAMESPACE cvc5::
  FILE cvc5JavaTargets.cmake
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/cvc5
  COMPONENT java-api
)
