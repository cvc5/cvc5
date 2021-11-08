###############################################################################
# Top contributors (to current version):
#   Mudathir Mohamed, Mathias Preiner, Aina Niemetz
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

# create directories
file(MAKE_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/io/github/cvc5/api")
set(JNI_DIR "${CMAKE_CURRENT_BINARY_DIR}/jni")
file(MAKE_DIRECTORY ${JNI_DIR})

# Generate Kind.java
configure_file(genkinds.py.in genkinds.py)

set(JAVA_KIND_FILE
  "${CMAKE_CURRENT_BINARY_DIR}/io/github/cvc5/api/Kind.java"
)

add_custom_command(
  OUTPUT
    ${JAVA_KIND_FILE}
  BYPRODUCTS
    ${JAVA_KIND_FILE}
  COMMAND
    "${PYTHON_EXECUTABLE}"
    "${CMAKE_CURRENT_BINARY_DIR}/genkinds.py"
    --kinds-header "${PROJECT_SOURCE_DIR}/src/api/cpp/cvc5_kind.h"
    --kinds-file-prefix "${CMAKE_CURRENT_BINARY_DIR}/io/github/cvc5/api/Kind"
  DEPENDS
    "${CMAKE_CURRENT_BINARY_DIR}/genkinds.py"
    "${PROJECT_SOURCE_DIR}/src/api/cpp/cvc5_kind.h"
)

add_custom_target(generate-java-kinds DEPENDS ${JAVA_KIND_FILE})

# find java
find_package(Java COMPONENTS Development REQUIRED)
include(UseJava)

# specify java source files
set(JAVA_FILES
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/AbstractPointer.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/CVC5ApiException.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/CVC5ApiOptionException.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/CVC5ApiRecoverableException.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/Datatype.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/DatatypeConstructor.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/DatatypeConstructorDecl.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/DatatypeDecl.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/DatatypeSelector.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/Grammar.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/IPointer.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/Op.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/OptionInfo.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/Pair.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/Result.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/RoundingMode.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/Solver.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/Sort.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/Stat.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/Statistics.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/Term.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/Triplet.java
  ${CMAKE_CURRENT_LIST_DIR}/io/github/cvc5/api/Utils.java
  ${JAVA_KIND_FILE}
)

# specify generated jni headers
set(JNI_HEADERS
  ${JNI_DIR}/io_github_cvc5_api_Solver.h
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
add_dependencies(generate-jni-headers generate-java-kinds)

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
  jni/term.cpp)

add_dependencies(cvc5jni generate-jni-headers)

target_include_directories(cvc5jni PUBLIC ${JNI_INCLUDE_DIRS})
target_include_directories(cvc5jni PUBLIC ${PROJECT_SOURCE_DIR}/src)
target_include_directories(cvc5jni PUBLIC ${CMAKE_BINARY_DIR}/src/)
target_include_directories(cvc5jni PUBLIC ${JNI_DIR})
target_link_libraries(cvc5jni PRIVATE ${JNI_LIBRARIES})
target_link_libraries(cvc5jni PRIVATE cvc5)

set(CVC5_JAR "cvc5-${CVC5_VERSION}.jar")

# create cvc5.jar file
add_jar(cvc5jar
  SOURCES
  ${JAVA_FILES}
  VERSION ${CVC5_VERSION}
  OUTPUT_NAME cvc5
)
set_target_properties(cvc5jar PROPERTIES SOURCES "${JAVA_FILES}")

add_dependencies(cvc5jar generate-java-kinds cvc5jni cvc5)
