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

# create directories
file(MAKE_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/src/main/java/cvc/")

# Generate cvc/Kind.java
configure_file(genkinds.py.in genkinds.py)
add_custom_target(
  gen-java-kinds
  ALL
  COMMAND
  "${PYTHON_EXECUTABLE}"
  "${CMAKE_CURRENT_BINARY_DIR}/genkinds.py"
  --kinds-header "${PROJECT_SOURCE_DIR}/src/api/cpp/cvc5_kind.h"
  --kinds-file-prefix "${CMAKE_CURRENT_BINARY_DIR}/src/main/java/cvc/Kind"
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
  ${CMAKE_CURRENT_LIST_DIR}/cvc/CVCApiException.java
  ${CMAKE_CURRENT_LIST_DIR}/cvc/CVCApiRecoverableException.java
  ${CMAKE_CURRENT_LIST_DIR}/cvc/IPointer.java
  ${CMAKE_CURRENT_LIST_DIR}/cvc/Solver.java
  ${CMAKE_CURRENT_LIST_DIR}/cvc/Utils.java
  ${CMAKE_CURRENT_BINARY_DIR}/src/main/java/cvc/Kind.java
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

add_library(cvcjni SHARED jni/cvc_Solver.cpp)
add_dependencies(cvcjni generate-jni-headers)

target_include_directories(cvcjni PUBLIC ${JNI_INCLUDE_DIRS})
target_include_directories(cvcjni PUBLIC ${PROJECT_SOURCE_DIR}/src)
target_include_directories(cvcjni PUBLIC ${CMAKE_BINARY_DIR}/src/)
target_include_directories(cvcjni PUBLIC ${CMAKE_CURRENT_BINARY_DIR}/jni)
target_link_libraries(cvcjni ${JNI_LIBRARIES})
target_link_libraries(cvcjni cvc4)

set(CVC_JAR "cvc-${CVC4_MAJOR}.${CVC4_MINOR}.${CVC4_RELEASE}.jar" CACHE STRING "cvc jar" FORCE)

# create cvc.jar file
add_jar(cvcjar
  SOURCES
  ${java_files}
  VERSION ${CVC4_MAJOR}.${CVC4_MINOR}.${CVC4_RELEASE}
  OUTPUT_NAME cvc
)

add_dependencies(cvcjar gen-java-kinds cvcjni cvc4)

set(CVC_JAR "${CMAKE_CURRENT_BINARY_DIR}/${CVC_JAR}" CACHE STRING "cvc jar" FORCE)
set(CVC_JNI_PATH "${CMAKE_CURRENT_BINARY_DIR}" CACHE STRING "cvc jni path" FORCE)