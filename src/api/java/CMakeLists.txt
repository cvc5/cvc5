###############################################################################
# Top contributors (to current version):
#   Mudathir Mohamed, Andres Noetzli, Andrew Reynolds
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

# Generate SortKind.java
set(JAVA_SORT_KIND_FILE
  "${CMAKE_CURRENT_BINARY_DIR}/io/github/cvc5/SortKind.java"
)
add_custom_command(
  OUTPUT
    ${JAVA_SORT_KIND_FILE}
  COMMAND
    "${Python_EXECUTABLE}"
    "${CMAKE_CURRENT_BINARY_DIR}/genenums.py"
    --enums-header "${PROJECT_SOURCE_DIR}/include/cvc5/cvc5_sort_kind.h"
    --java-api-path "${CMAKE_CURRENT_BINARY_DIR}/io/github/"
  DEPENDS
    "${CMAKE_CURRENT_BINARY_DIR}/genenums.py"
    "${PROJECT_SOURCE_DIR}/src/api/parseenums.py"
    "${PROJECT_SOURCE_DIR}/include/cvc5/cvc5_sort_kind.h"
)
add_custom_target(generate-java-sort-kinds DEPENDS ${JAVA_SORT_KIND_FILE})

set(JAVA_TYPES_FILES
  "${CMAKE_CURRENT_BINARY_DIR}/io/github/cvc5/modes/BlockModelsMode.java"
  "${CMAKE_CURRENT_BINARY_DIR}/io/github/cvc5/modes/LearnedLitType.java"
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
find_package(Java COMPONENTS Development REQUIRED)
include(UseJava)

# specify java source files
set(JAVA_FILES
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/AbstractPointer.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Context.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/CVC5ApiException.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/CVC5ApiOptionException.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/CVC5ApiRecoverableException.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Datatype.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/DatatypeConstructor.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/DatatypeConstructorDecl.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/DatatypeDecl.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/DatatypeSelector.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Grammar.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/IOracle.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/IPointer.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Op.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/OptionInfo.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Pair.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Result.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Solver.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Sort.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Stat.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Statistics.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/SynthResult.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Term.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Triplet.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/Utils.java
  ${JAVA_KIND_FILE}
  ${JAVA_SORT_KIND_FILE}
)

# specify generated jni headers
set(JNI_HEADERS
  ${JNI_DIR}/io_github_cvc5_DatatypeConstructorDecl.h
  ${JNI_DIR}/io_github_cvc5_DatatypeConstructor.h
  ${JNI_DIR}/io_github_cvc5_DatatypeDecl.h
  ${JNI_DIR}/io_github_cvc5_Datatype.h
  ${JNI_DIR}/io_github_cvc5_DatatypeSelector.h
  ${JNI_DIR}/io_github_cvc5_Grammar.h
  ${JNI_DIR}/io_github_cvc5_Op.h
  ${JNI_DIR}/io_github_cvc5_OptionInfo.h
  ${JNI_DIR}/io_github_cvc5_Result.h
  ${JNI_DIR}/io_github_cvc5_Solver.h
  ${JNI_DIR}/io_github_cvc5_Sort.h
  ${JNI_DIR}/io_github_cvc5_Stat.h
  ${JNI_DIR}/io_github_cvc5_Statistics.h
  ${JNI_DIR}/io_github_cvc5_SynthResult.h
  ${JNI_DIR}/io_github_cvc5_Term.h
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
add_dependencies(generate-jni-headers generate-java-kinds generate-java-sort-kinds generate-java-types)

# find jni package
find_package(JNI REQUIRED)
message(STATUS "JAVA_AWT_LIBRARY     : ${JAVA_AWT_LIBRARY}")
message(STATUS "JNI_INCLUDE_DIRS     : ${JNI_INCLUDE_DIRS}")
message(STATUS "JNI_LIBRARIES        : ${JNI_LIBRARIES} ")
message(STATUS "JNI_FOUND            : ${JNI_FOUND}")
message(STATUS "JAVA_AWT_LIBRARY     : ${JAVA_AWT_LIBRARY}")
message(STATUS "JAVA_JVM_LIBRARY     : ${JAVA_JVM_LIBRARY}")
message(STATUS "JAVA_INCLUDE_PATH    : ${JAVA_INCLUDE_PATH}")
message(STATUS "JAVA_INCLUDE_PATH2   : ${JAVA_INCLUDE_PATH2}")
message(STATUS "JAVA_AWT_INCLUDE_PATH: ${JAVA_AWT_INCLUDE_PATH}")

add_library(cvc5jni
  jni/api_utilities.cpp
  jni/datatype.cpp
  jni/datatype_constructor.cpp
  jni/datatype_constructor_decl.cpp
  jni/datatype_decl.cpp
  jni/datatype_selector.cpp
  jni/grammar.cpp
  jni/op.cpp
  jni/option_info.cpp
  jni/result.cpp
  jni/solver.cpp
  jni/sort.cpp
  jni/stat.cpp
  jni/statistics.cpp
  jni/synth_result.cpp
  jni/term.cpp)

add_dependencies(cvc5jni generate-jni-headers)

target_include_directories(cvc5jni PUBLIC ${JNI_INCLUDE_DIRS})
target_include_directories(cvc5jni PUBLIC ${PROJECT_SOURCE_DIR}/src)
target_include_directories(cvc5jni PUBLIC ${CMAKE_BINARY_DIR}/src/)
target_include_directories(cvc5jni PUBLIC ${JNI_DIR})
target_link_libraries(cvc5jni PRIVATE cvc5)

set(CVC5_JAR "cvc5-${CVC5_VERSION}.jar")

# create cvc5.jar file
add_jar(cvc5jar
  SOURCES
  ${JAVA_FILES}
  VERSION ${CVC5_VERSION}
  OUTPUT_NAME cvc5
)

add_dependencies(cvc5jar generate-java-kinds cvc5jni cvc5)

# install in the same directory of cvc5-targets
install(TARGETS cvc5jni
  LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
  ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
)

install_jar(cvc5jar DESTINATION share/java)

install_jar_exports(
  TARGETS cvc5jar
  NAMESPACE cvc5::
  FILE cvc5JavaTargets.cmake
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/cvc5
)
