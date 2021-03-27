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
file(MAKE_DIRECTORY
  "${CMAKE_CURRENT_BINARY_DIR}/src/main/resources"
  "${CMAKE_CURRENT_BINARY_DIR}/src/main/java"
  "${CMAKE_CURRENT_BINARY_DIR}/src/test/java"
  )


# find jni package
find_package(JNI REQUIRED)

# specify the output destination of cvcjni library
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/src/main/resources")

add_library(cvcjni SHARED jni/cvc_Solver.cpp)

target_include_directories(cvcjni PUBLIC ${JNI_INCLUDE_DIRS})
target_include_directories(cvcjni PUBLIC "${CMAKE_INSTALL_PREFIX}/include")
target_link_libraries(cvcjni ${JNI_LIBRARIES})
target_link_libraries(cvcjni cvc4)


# copy libraries and java files
add_custom_target(copy-java-api-files
  COMMAND
    # copy library file: libcvc4.so.7
    ${CMAKE_COMMAND} -E  copy
      $<TARGET_FILE:cvc4> "${CMAKE_CURRENT_BINARY_DIR}/src/main/resources"
  COMMAND
    # copy library file: libcvcjni.so
    ${CMAKE_COMMAND} -E  copy
      $<TARGET_FILE:cvcjni> "${CMAKE_CURRENT_BINARY_DIR}/src/main/resources"
  COMMAND
    # copy java source files
    ${CMAKE_COMMAND} -E copy_directory
    "${CMAKE_CURRENT_LIST_DIR}/cvc" "${CMAKE_CURRENT_BINARY_DIR}/src/main/java/cvc"
  COMMAND
    # copy java test files
    ${CMAKE_COMMAND} -E copy_directory
    "${CMAKE_SOURCE_DIR}/test/unit/api/java/cvc" "${CMAKE_CURRENT_BINARY_DIR}/src/test/java/cvc"
  COMMAND
    # copy build.gradle
    ${CMAKE_COMMAND} -E copy
    "${CMAKE_CURRENT_LIST_DIR}/build.gradle" ${CMAKE_CURRENT_BINARY_DIR}
  )

add_dependencies(copy-java-api-files cvc4 cvcjni)

# Generate cvc/Kind.java
add_custom_target(
  gen-java-kinds
  ALL
  COMMAND
    "${PYTHON_EXECUTABLE}"
    "${CMAKE_CURRENT_LIST_DIR}/genkinds.py"
    --kinds-header "${PROJECT_SOURCE_DIR}/src/api/cvc4cppkind.h"
    --kinds-file-prefix "${CMAKE_CURRENT_BINARY_DIR}/src/main/java/cvc/Kind"
  DEPENDS
  genkinds.py
  COMMENT
  "Generate Kind.java"
)

add_dependencies(gen-java-kinds copy-java-api-files)

# run gradle
add_custom_target(
  gradle-build
  ALL
  COMMAND
    # run gradlew build without running the test task
    ${PROJECT_SOURCE_DIR}/src/api/java/gradlew -p ${CMAKE_CURRENT_BINARY_DIR} build -x test
  COMMENT "Run gradlew build"
  VERBATIM
)

add_dependencies(gradle-build cvcjni gen-java-kinds)