###############################################################################
# Top contributors (to current version):
#   Daniel Larraz, Mudathir Mohamed, Andres Noetzli
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

# create directories
file(MAKE_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/io/github/cvc5/api")
set(JNI_DIR "${CMAKE_CURRENT_BINARY_DIR}/jni")
file(MAKE_DIRECTORY ${JNI_DIR})

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

# find java
find_package(Java 1.8 COMPONENTS Development REQUIRED)
include(UseJava)

# specify java source files
set(JAVA_FILES
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/AbstractPointer.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/AbstractPlugin.java
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
  ${JAVA_KIND_FILE}
  ${JAVA_PROOF_RULE_FILE}
  ${JAVA_SKOLEM_FUN_ID_FILE}
  ${JAVA_SORT_KIND_FILE}
  ${JAVA_TYPES_FILES}
)

# specify generated jni headers
set(JNI_HEADERS
  ${JNI_DIR}/io_github_cvc5_DatatypeConstructorDecl.h
  ${JNI_DIR}/io_github_cvc5_DatatypeConstructor.h
  ${JNI_DIR}/io_github_cvc5_DatatypeDecl.h
  ${JNI_DIR}/io_github_cvc5_Datatype.h
  ${JNI_DIR}/io_github_cvc5_DatatypeSelector.h
  ${JNI_DIR}/io_github_cvc5_Grammar.h
  ${JNI_DIR}/io_github_cvc5_InputParser.h
  ${JNI_DIR}/io_github_cvc5_Op.h
  ${JNI_DIR}/io_github_cvc5_OptionInfo.h
  ${JNI_DIR}/io_github_cvc5_Proof.h
  ${JNI_DIR}/io_github_cvc5_Result.h
  ${JNI_DIR}/io_github_cvc5_Solver.h
  ${JNI_DIR}/io_github_cvc5_Sort.h
  ${JNI_DIR}/io_github_cvc5_Stat.h
  ${JNI_DIR}/io_github_cvc5_Statistics.h
  ${JNI_DIR}/io_github_cvc5_SynthResult.h
  ${JNI_DIR}/io_github_cvc5_Term.h
  ${JNI_DIR}/io_github_cvc5_TermManager.h
)

# generate jni headers
add_custom_command(
  OUTPUT
    ${JNI_HEADERS}
  COMMAND
    # generate jni header files
    ${Java_JAVAC_EXECUTABLE} -h ${JNI_DIR} ${JAVA_FILES} -d ${JNI_DIR}
  DEPENDS
    ${JAVA_FILES}
  COMMENT "Generate jni headers"
  VERBATIM
)

add_custom_target(generate-jni-headers DEPENDS ${JNI_HEADERS})
add_dependencies(generate-jni-headers generate-java-kinds generate-java-types generate-java-proofrules generate-java-skolemfunids)

# JNI_HOME, if defined, specifies the path to the JNI libraries
if(NOT DEFINED JNI_HOME AND DEFINED ENV{JNI_HOME})
  set(JNI_HOME $ENV{JNI_HOME})
endif()

if(NOT DEFINED JAVA_HOME AND NOT DEFINED JNI_HOME AND NOT WIN32)
  # If there are multiple versions of Java on the system,
  # CMake might find a version of JNI that differs from
  # the version of the Java executable. To address this,
  # we retrieve the java.home from the JVM settings and
  # set the JAVA_HOME variable.
  # This approach works properly on Unix systems but
  # not on Windows.
  execute_process(
    COMMAND ${Java_JAVA_EXECUTABLE} -XshowSettings:runtime -version
    OUTPUT_VARIABLE java_settings
    ERROR_VARIABLE java_settings
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )
  # Extract the line containing "java.home"
  string(REGEX MATCH "java.home = [^\r\n]+" java_home_line "${java_settings}")
  # Extract the path from the line
  string(REPLACE "java.home = " "" JAVA_HOME "${java_home_line}")
  message(STATUS "JAVA_HOME: ${JAVA_HOME}")
endif()

if(DEFINED JNI_HOME)
  message(STATUS "JNI_HOME: ${JNI_HOME}")
  set(JAVA_HOME "${JNI_HOME}") # FindJNI uses JAVA_HOME
  if(CMAKE_CROSSCOMPILING OR CMAKE_CROSSCOMPILING_MACOS)
    # If cross-compiling, we need to set the JNI variables manually
    if(CMAKE_SYSTEM_NAME STREQUAL "Windows")
      set(JAVA_AWT_LIBRARY "${JAVA_HOME}/lib/jawt.lib")
      set(JAVA_JVM_LIBRARY "${JAVA_HOME}/lib/server/jvm.lib")
      set(JAVA_INCLUDE_PATH "${JAVA_HOME}/include/")
      set(JAVA_INCLUDE_PATH2 "${JAVA_HOME}/include/win32")
      set(JAVA_AWT_INCLUDE_PATH "${JAVA_HOME}/include")
    elseif(CMAKE_SYSTEM_NAME STREQUAL "Darwin")
      set(JAVA_AWT_LIBRARY "${JAVA_HOME}/lib/libjawt.dylib")
      set(JAVA_JVM_LIBRARY "${JAVA_HOME}/lib/server/libjvm.dylib")
      set(JAVA_INCLUDE_PATH "${JAVA_HOME}/include/")
      set(JAVA_INCLUDE_PATH2 "${JAVA_HOME}/include/darwin")
      set(JAVA_AWT_INCLUDE_PATH "${JAVA_HOME}/include")
    else()
      set(JAVA_AWT_LIBRARY "${JAVA_HOME}/lib/libjawt.so")
      set(JAVA_JVM_LIBRARY "${JAVA_HOME}/lib/server/libjvm.so")
      set(JAVA_INCLUDE_PATH "${JAVA_HOME}/include/")
      set(JAVA_INCLUDE_PATH2 "${JAVA_HOME}/include/linux")
      set(JAVA_AWT_INCLUDE_PATH "${JAVA_HOME}/include")
    endif()
  endif()
endif()

if(BUILD_SHARED_LIBS)
  # Find JNI package
  find_package(JNI REQUIRED)
else()
  # When a static build is enabled, we still build a JNI shared library,
  # but all cvc5 dependencies are statically linked to it. To do that,
  # we need to find the shared JNI libraries for Java.
  # Save the original suffixes
  set(_original_suffixes "${CMAKE_FIND_LIBRARY_SUFFIXES}")
  # Temporarily add appropriate suffixes to find JNI libraries
  if (WIN32)
    list(APPEND CMAKE_FIND_LIBRARY_SUFFIXES .dll)
  else()
    list(APPEND CMAKE_FIND_LIBRARY_SUFFIXES .so .dylib)
  endif()
  # Find JNI package
  find_package(JNI REQUIRED)
  # Restore the original suffixes
  set(CMAKE_FIND_LIBRARY_SUFFIXES "${_original_suffixes}")
endif()

message(STATUS "JNI_FOUND            : ${JNI_FOUND}")
message(STATUS "JNI_INCLUDE_DIRS     : ${JNI_INCLUDE_DIRS}")
message(STATUS "JNI_LIBRARIES        : ${JNI_LIBRARIES} ")
message(STATUS "JAVA_AWT_LIBRARY     : ${JAVA_AWT_LIBRARY}")
message(STATUS "JAVA_JVM_LIBRARY     : ${JAVA_JVM_LIBRARY}")
message(STATUS "JAVA_INCLUDE_PATH    : ${JAVA_INCLUDE_PATH}")
message(STATUS "JAVA_INCLUDE_PATH2   : ${JAVA_INCLUDE_PATH2}")
message(STATUS "JAVA_AWT_INCLUDE_PATH: ${JAVA_AWT_INCLUDE_PATH}")

set(jni_files
  jni/api_plugin.cpp
  jni/api_plugin.h
  jni/api_solver.cpp
  jni/api_solver.h
  jni/api_utilities.cpp
  jni/datatype.cpp
  jni/command.cpp
  jni/datatype_constructor_decl.cpp
  jni/datatype_constructor.cpp
  jni/datatype_decl.cpp
  jni/datatype_selector.cpp
  jni/grammar.cpp
  jni/input_parser.cpp
  jni/op.cpp
  jni/option_info.cpp
  jni/proof.cpp
  jni/result.cpp
  jni/solver.cpp
  jni/sort.cpp
  jni/stat.cpp
  jni/statistics.cpp
  jni/symbol_manager.cpp
  jni/synth_result.cpp
  jni/term.cpp
  jni/term_manager.cpp)

# Enforce the build of a shared library
add_library(cvc5jni SHARED ${jni_files})
add_dependencies(cvc5jni generate-jni-headers)

if(WIN32 AND NOT BUILD_SHARED_LIBS)
  # Ensure that cvc5jni does not expect DLL imports,
  # but static linking
  target_compile_definitions(cvc5jni PRIVATE CVC5_STATIC_DEFINE)
endif()

target_include_directories(cvc5jni PUBLIC ${JNI_INCLUDE_DIRS})
target_include_directories(cvc5jni PUBLIC ${PROJECT_SOURCE_DIR}/src)
target_include_directories(cvc5jni PUBLIC ${CMAKE_BINARY_DIR}/src/)
target_include_directories(cvc5jni PUBLIC ${JNI_DIR})
target_link_libraries(cvc5jni PRIVATE cvc5 cvc5parser)

if (WIN32 AND NOT BUILD_SHARED_LIBS)
  # Statically link all libraries, including MinGW-w64 libraries
  set_target_properties(cvc5jni PROPERTIES LINK_FLAGS -static)
  set_target_properties(cvc5jni PROPERTIES LINK_SEARCH_START_STATIC ON)
  set_target_properties(cvc5jni PROPERTIES LINK_SEARCH_END_STATIC ON)
endif()

# Java on Windows expects the JNI libraries without the prefix
if (WIN32)
  set_target_properties(cvc5jni PROPERTIES PREFIX "")
  set_target_properties(cvc5jni PROPERTIES IMPORT_PREFIX "")
endif()

set(CVC5_JAR "cvc5-${CVC5_VERSION}.jar")

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
    VERSION ${CVC5_VERSION}
    OUTPUT_NAME cvc5
  )
endif()

add_dependencies(cvc5jar generate-java-kinds cvc5jni cvc5 cvc5parser)

# Install in the same directory of cvc5-targets.
# On Windows, CMake's default install action places
# DLLs into the runtime path (by default "bin")
install(TARGETS cvc5jni COMPONENT java-api)

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
