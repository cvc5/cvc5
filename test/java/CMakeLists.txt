find_package(Java REQUIRED)
find_package(JUnit 4.0 REQUIRED)
include(UseJava)

set(java_test_src_files
  BitVectors.java
  BitVectorsAndArrays.java
  Combination.java
  HelloWorld.java
  Issue2846.java
  LinearArith.java
)

add_jar(build-javatests
  SOURCES ${java_test_src_files}
  INCLUDE_JARS
    ${CMAKE_BINARY_DIR}/src/bindings/java/CVC4.jar
    ${JUnit_JAR}
  OUTPUT_NAME javatests
)
add_dependencies(build-javatests cvc4jar)
add_dependencies(build-tests build-javatests)

# Add java tests to ctest
set(classpath "${CMAKE_CURRENT_BINARY_DIR}/javatests.jar")
set(classpath "${classpath}:${CMAKE_BINARY_DIR}/src/bindings/java/CVC4.jar")
set(classpath "${classpath}:${JUnit_JAR}:${JUnit_JAR_DEPS}")

foreach(src_file ${java_test_src_files})
  string(REPLACE ".java" "" name ${src_file})
  add_test(
    NAME ${name}
    COMMAND
      ${Java_JAVA_EXECUTABLE}
        -Djava.library.path=${CMAKE_BINARY_DIR}/src/bindings/java/
        -cp ${classpath}
        org.junit.runner.JUnitCore
        ${name}
  )
  set_tests_properties(${name} PROPERTIES LABELS "java")
endforeach()
