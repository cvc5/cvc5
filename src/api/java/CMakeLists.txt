###############################################################################
# Top contributors (to current version):
#   Mudathir Mohamed, Mathias Preiner, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

# create a directory for the cvc package
file(MAKE_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/cvc")

# Generate cvc/Kind.java
configure_file(genkinds.py.in genkinds.py)
add_custom_target(
  gen-java-kinds
  ALL
  COMMAND
    "${PYTHON_EXECUTABLE}"
    "${CMAKE_CURRENT_BINARY_DIR}/genkinds.py"
    --kinds-header "${PROJECT_SOURCE_DIR}/src/api/cpp/cvc5_kind.h"
    --kinds-file-prefix "${CMAKE_CURRENT_BINARY_DIR}/cvc/Kind"
  DEPENDS
    "${CMAKE_CURRENT_BINARY_DIR}/genkinds.py"
  COMMENT
    "Generate Kind.java"
)
