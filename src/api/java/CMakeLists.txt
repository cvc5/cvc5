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

# copy cvc libraries to the resource directory
file(GLOB CVC_LIBS "${CMAKE_INSTALL_PREFIX}/lib/*.so*")
file(COPY ${CVC_LIBS} DESTINATION "${CMAKE_CURRENT_BINARY_DIR}/src/main/resources")
file(COPY  "${CMAKE_CURRENT_LIST_DIR}/cvc" DESTINATION "${CMAKE_CURRENT_BINARY_DIR}/src/main/java")
file(COPY  "/home/mudathir/Desktop/CVC4/mudathir/test/api/java/cvc" DESTINATION "${CMAKE_CURRENT_BINARY_DIR}/src/test/java")
# copy gradle files
file(COPY  "${CMAKE_CURRENT_LIST_DIR}/gradle" DESTINATION ${CMAKE_CURRENT_BINARY_DIR})
file(COPY  "${CMAKE_CURRENT_LIST_DIR}/gradlew" DESTINATION ${CMAKE_CURRENT_BINARY_DIR})
file(COPY  "${CMAKE_CURRENT_LIST_DIR}/build.gradle" DESTINATION ${CMAKE_CURRENT_BINARY_DIR})
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


get_cmake_property(_variableNames VARIABLES)
list (SORT _variableNames)
foreach (_variableName ${_variableNames})
    message(STATUS "${_variableName}=${${_variableName}}")
endforeach()

#message("I am here: ${CMAKE_BINARY_DIR}")
#message("I am here: ${CMAKE_CURRENT_BINARY_DIR}")
#message("I am here: ${Java_JAR_EXECUTABLE}")
#message("I am here: ${Java_JAVAC_EXECUTABLE}")
#message("I am here: ${JAVA_CVC_DIR}")
#message("I am here: ${CMAKE_INSTALL_PREFIX}")

find_package(Java)
include(UseJava)

find_package(JNI)
message(STATUS "JNI_INCLUDE_DIRS=${JNI_INCLUDE_DIRS}")
include_directories(${JNI_INCLUDE_DIRS})
message(STATUS "JNI_LIBRARIES=${JNI_LIBRARIES}")
link_directories(${JNI_LIBRARIES})

include_directories("${CMAKE_INSTALL_PREFIX}/include")
link_directories("${CMAKE_INSTALL_PREFIX}/lib")

set(CMAKE_LIBRARY_OUTPUT_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/src/main/resources")

add_library(cvcJavaApi SHARED
        jni/cvc_Configuration.cpp
        jni/cvc_Datatype.cpp
        jni/cvc_DatatypeConstructorDecl.cpp
        jni/cvc_DatatypeDecl.cpp
        jni/cvc_Op.cpp
        jni/cvc_Result.cpp
        jni/cvc_Solver.cpp
        jni/cvc_Sort.cpp
        jni/cvc_Term.cpp)
target_link_libraries(cvcJavaApi cvc4)

