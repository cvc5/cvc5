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
file(MAKE_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/cvc")

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
