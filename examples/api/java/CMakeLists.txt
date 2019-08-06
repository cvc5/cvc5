set(EXAMPLES_API_JAVA_BIN_DIR ${EXAMPLES_BIN_DIR}/api/java) 
file(MAKE_DIRECTORY ${EXAMPLES_API_JAVA_BIN_DIR})

set(EXAMPLES_API_JAVA
  BitVectors
  BitVectorsAndArrays
  ## disabled until bindings for the new API are in place (issue #2284)
  #CVC4Streams
  Combination
  Datatypes
  FloatingPointArith
  HelloWorld
  LinearArith
  ## disabled until bindings for the new API are in place (issue #2284)
  #PipedInput
  Statistics
  Strings
  UnsatCores
)

foreach(example ${EXAMPLES_API_JAVA})
  add_custom_target(${example}
    COMMAND
      ${Java_JAVAC_EXECUTABLE}
        -cp ${EXAMPLES_JAVA_CLASSPATH} ${CMAKE_CURRENT_SOURCE_DIR}/${example}.java
        -d ${EXAMPLES_API_JAVA_BIN_DIR}
    DEPENDS cvc4jar)
  add_dependencies(examples ${example})
  set(example_test example/api/java/${example})
  add_test(
    NAME ${example_test}
    COMMAND
      ${Java_JAVA_EXECUTABLE}
        -Djava.library.path=${CMAKE_BINARY_DIR}/src/bindings/java/
        -cp "${EXAMPLES_JAVA_CLASSPATH}:${CMAKE_BINARY_DIR}/bin/examples/api/java/"
        ${example}
  )
  set_tests_properties(${example_test} PROPERTIES SKIP_RETURN_CODE 77)
  set_tests_properties(${example_test} PROPERTIES LABELS "example")
endforeach()
