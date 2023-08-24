###############################################################################
# Top contributors (to current version):
#   Mudathir Mohamed, Aina Niemetz, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

set(EXAMPLES_API_JAVA
   Bags
   BitVectors
   BitVectorsAndArrays
   Combination
   Datatypes
   Exceptions
   Extract
   FloatingPointArith
   HelloWorld
   LinearArith
   QuickStart
   Relations
   Sequences
   Sets
   Statistics
   Strings
   SygusFun
   SygusInv
   Transcendentals
   UnsatCores
)

function(add_java_example example)
  add_jar(${example} ${example}.java
          INCLUDE_JARS "${CVC5_JAR}"
          OUTPUT_DIR "${CMAKE_BINARY_DIR}/bin/api/java")

  set(EXAMPLE_TEST_NAME api/java/${example})

  add_test(
    NAME ${EXAMPLE_TEST_NAME}
    COMMAND
      ${Java_JAVA_EXECUTABLE}
        -cp "${CVC5_JAR}:${CMAKE_BINARY_DIR}/bin/api/java/${example}.jar"
        -Djava.library.path=${CVC5_JNI_PATH}
        ${example}
  )
  set_tests_properties(${EXAMPLE_TEST_NAME} PROPERTIES SKIP_RETURN_CODE 77)
endfunction()

foreach(example ${EXAMPLES_API_JAVA})
  add_java_example(${example})
endforeach()

if(USE_COCOA)
  add_java_example(FiniteField)
endif()
