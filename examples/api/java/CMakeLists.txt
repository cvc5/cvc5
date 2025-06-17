###############################################################################
# Top contributors (to current version):
#   Mudathir Mohamed, Aina Niemetz, Daniel Larraz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

set(EXAMPLES_API_JAVA
   BitVectors
   BitVectorsAndArrays
   Combination
   Datatypes
   Exceptions
   Extract
   HelloWorld
   LinearArith
   QuickStart
   Sequences
   Sets
   Statistics
   Strings
   SygusFun
   SygusInv
   UnsatCores
   Uf
)

function(add_java_example example)
  add_jar(${example} ${example}.java
          INCLUDE_JARS "${CVC5_JAR}"
          OUTPUT_DIR "${CMAKE_BINARY_DIR}/bin/api/java")

  set(EXAMPLE_TEST_NAME api/java/${example})

  if(WIN32)
    set(PATH_SEP ";")
  else()
    set(PATH_SEP ":")
  endif()

  add_test(
    NAME ${EXAMPLE_TEST_NAME}
    COMMAND
      ${Java_JAVA_EXECUTABLE}
        -cp "${CVC5_JAR}${PATH_SEP}${CMAKE_BINARY_DIR}/bin/api/java/${example}.jar"
        -Djava.library.path=${CVC5_JNI_PATH}
        ${example}
  )
  set_tests_properties(${EXAMPLE_TEST_NAME} PROPERTIES SKIP_RETURN_CODE 77)
endfunction()

foreach(example ${EXAMPLES_API_JAVA})
  add_java_example(${example})
endforeach()

if(NOT CVC5_SAFE_BUILD)
  add_java_example(FloatingPointArith)
  add_java_example(Bags)
  add_java_example(Relations)
  add_java_example(Transcendentals)
endif()

if(CVC5_USE_COCOA)
  add_java_example(FiniteField)
endif()
