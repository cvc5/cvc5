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

# create a directory for the cvc package
set(JAVA_CVC_DIR "${CMAKE_CURRENT_BINARY_DIR}/cvc")
# copy java files into cvc directory
file(COPY  "${CMAKE_CURRENT_LIST_DIR}/cvc" DESTINATION ${CMAKE_CURRENT_BINARY_DIR})
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
    --kinds-file-prefix "${CMAKE_CURRENT_BINARY_DIR}/cvc/Kind"
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

message("I am here: ${CMAKE_BINARY_DIR}")
message("I am here: ${CMAKE_CURRENT_BINARY_DIR}")
message("I am here: ${Java_JAR_EXECUTABLE}")
message("I am here: ${Java_JAVAC_EXECUTABLE}")
message("I am here: ${JAVA_CVC_DIR}")
message("I am here: ${${CMAKE_INSTALL_PREFIX}}")
find_package(Java)
include(UseJava)

find_package(JNI)
message(STATUS "JNI_INCLUDE_DIRS=${JNI_INCLUDE_DIRS}")
include_directories(${JNI_INCLUDE_DIRS})
message(STATUS "JNI_LIBRARIES=${JNI_LIBRARIES}")
link_directories(${JNI_LIBRARIES})

include_directories("${CMAKE_INSTALL_PREFIX}/include")
link_directories("${CMAKE_INSTALL_PREFIX}/lib")

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

#add_custom_command()

#add_jar(cvcJavaApi
#        SOURCES cvc/Op.java cvc/Solver.java
#        INCLUDE "../../../../build/src/libcvc4.so.7"
#        )
