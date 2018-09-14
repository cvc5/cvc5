set(EXAMPLES_API_JAVA_BIN_DIR ${EXAMPLES_API_BIN_DIR}/java) 
file(MAKE_DIRECTORY ${EXAMPLES_API_JAVA_BIN_DIR})

add_custom_target(BitVectorsjava
  COMMAND
    ${Java_JAVAC_EXECUTABLE}
      -cp ${EXAMPLES_JAVA_CLASSPATH} ${CMAKE_CURRENT_SOURCE_DIR}/BitVectors.java
      -d ${EXAMPLES_API_JAVA_BIN_DIR}
  DEPENDS cvc4jar)
add_dependencies(examples BitVectorsjava)

add_custom_target(BitVectorsAndArraysjava
  COMMAND
    ${Java_JAVAC_EXECUTABLE}
      -cp ${EXAMPLES_JAVA_CLASSPATH} ${CMAKE_CURRENT_SOURCE_DIR}/BitVectorsAndArrays.java
      -d ${EXAMPLES_API_JAVA_BIN_DIR}
  DEPENDS cvc4jar)
add_dependencies(examples BitVectorsAndArraysjava)

## disabled until bindings for the new API are in place (issue #2284)
#  add_custom_target(CVC4Streamsjava
#    COMMAND
#      ${Java_JAVAC_EXECUTABLE}
#        -cp ${EXAMPLES_JAVA_CLASSPATH} ${CMAKE_CURRENT_SOURCE_DIR}/CVC4Streams.java
#        -d ${CMAKE_BINARY_DIR}/bin/examples/api/java
#    DEPENDS cvc4jar)
#  add_dependencies(examples CVC4Streamsjava)

add_custom_target(Combinationjava
  COMMAND
    ${Java_JAVAC_EXECUTABLE}
      -cp ${EXAMPLES_JAVA_CLASSPATH} ${CMAKE_CURRENT_SOURCE_DIR}/Combination.java
      -d ${EXAMPLES_API_JAVA_BIN_DIR}
  DEPENDS cvc4jar)
add_dependencies(examples Combinationjava)

add_custom_target(Datatypesjava
  COMMAND
    ${Java_JAVAC_EXECUTABLE}
      -cp ${EXAMPLES_JAVA_CLASSPATH} ${CMAKE_CURRENT_SOURCE_DIR}/Datatypes.java
      -d ${EXAMPLES_API_JAVA_BIN_DIR}
  DEPENDS cvc4jar)
add_dependencies(examples Datatypesjava)

add_custom_target(HelloWorldjava
  COMMAND
    ${Java_JAVAC_EXECUTABLE}
      -cp ${EXAMPLES_JAVA_CLASSPATH} ${CMAKE_CURRENT_SOURCE_DIR}/HelloWorld.java
      -d ${EXAMPLES_API_JAVA_BIN_DIR}
  DEPENDS cvc4jar)
add_dependencies(examples HelloWorldjava)

add_custom_target(LinearArithjava
  COMMAND
    ${Java_JAVAC_EXECUTABLE}
      -cp ${EXAMPLES_JAVA_CLASSPATH} ${CMAKE_CURRENT_SOURCE_DIR}/LinearArith.java
      -d ${EXAMPLES_API_JAVA_BIN_DIR}
  DEPENDS cvc4jar)
add_dependencies(examples LinearArithjava)

## disabled until bindings for the new API are in place (issue #2284)
#  add_custom_target(PipedInputjava
#    COMMAND
#      ${Java_JAVAC_EXECUTABLE}
#        -cp ${EXAMPLES_JAVA_CLASSPATH} ${CMAKE_CURRENT_SOURCE_DIR}/PipedInput.java
#        -d ${EXAMPLES_API_JAVA_BIN_DIR}
#    DEPENDS cvc4jar)
#  add_dependencies(examples PipedInputjava)

add_custom_target(Stringsjava
  COMMAND
    ${Java_JAVAC_EXECUTABLE}
      -cp ${EXAMPLES_JAVA_CLASSPATH} ${CMAKE_CURRENT_SOURCE_DIR}/Strings.java
      -d ${EXAMPLES_API_JAVA_BIN_DIR}
  DEPENDS cvc4jar)
add_dependencies(examples Stringsjava)
