#####################
## CMakeLists.txt
## Top contributors (to current version):
##   Mudathir Mohamed
## This file is part of the CVC5 project.
## Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##

# create directories
file(MAKE_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/src/main/java/cvc5/")
file(MAKE_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/jni")

# Generate cvc5/Kind.java
configure_file(genkinds.py.in genkinds.py)
add_custom_target(
  gen-java-kinds
  ALL
  COMMAND
  "${PYTHON_EXECUTABLE}"
  "${CMAKE_CURRENT_BINARY_DIR}/genkinds.py"
  --kinds-header "${PROJECT_SOURCE_DIR}/src/api/cpp/cvc5_kind.h"
  --kinds-file-prefix "${CMAKE_CURRENT_BINARY_DIR}/src/main/java/cvc5/Kind"
  DEPENDS
  "${CMAKE_CURRENT_BINARY_DIR}/genkinds.py"
  COMMENT
  "Generate Kind.java"
)

# find java
find_package(Java COMPONENTS Development REQUIRED)
include(UseJava)

# specify java source files
set(java_files
  ${CMAKE_CURRENT_LIST_DIR}/cvc5/CVC5ApiException.java
  ${CMAKE_CURRENT_LIST_DIR}/cvc5/CVC5ApiRecoverableException.java
  ${CMAKE_CURRENT_LIST_DIR}/cvc5/IPointer.java
  ${CMAKE_CURRENT_LIST_DIR}/cvc5/Solver.java
  ${CMAKE_CURRENT_LIST_DIR}/cvc5/Utils.java
  ${CMAKE_CURRENT_BINARY_DIR}/src/main/java/cvc5/Kind.java
)

# generate jni headers
add_custom_target(
  generate-jni-headers
  ALL
  COMMAND
  # generate jni header files
  ${Java_JAVAC_EXECUTABLE} -h jni ${java_files} -d jni
  COMMENT "Generate jni headers"
  VERBATIM
)

add_dependencies(generate-jni-headers gen-java-kinds)

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

add_library(cvc5jni SHARED jni/cvc5_Solver.cpp)
add_dependencies(cvc5jni generate-jni-headers)

target_include_directories(cvc5jni PUBLIC ${JNI_INCLUDE_DIRS})
target_include_directories(cvc5jni PUBLIC ${PROJECT_SOURCE_DIR}/src)
target_include_directories(cvc5jni PUBLIC ${CMAKE_BINARY_DIR}/src/)
target_include_directories(cvc5jni PUBLIC ${CMAKE_CURRENT_BINARY_DIR}/jni)
target_link_libraries(cvc5jni ${JNI_LIBRARIES})
target_link_libraries(cvc5jni cvc4)

set(CVC5_JAR "cvc5-${CVC4_MAJOR}.${CVC4_MINOR}.${CVC4_RELEASE}.jar" CACHE STRING "cvc5 jar" FORCE)

# create cvc5.jar file
add_jar(cvc5jar
  SOURCES
  ${java_files}
  VERSION ${CVC4_MAJOR}.${CVC4_MINOR}.${CVC4_RELEASE}
  OUTPUT_NAME cvc5
)

add_dependencies(cvc5jar gen-java-kinds cvc5jni cvc4)

set(CVC5_JAR "${CMAKE_CURRENT_BINARY_DIR}/${CVC5_JAR}" CACHE STRING "cvc5 jar" FORCE)
set(CVC5_JNI_PATH "${CMAKE_CURRENT_BINARY_DIR}" CACHE STRING "cvc5 jni path" FORCE)