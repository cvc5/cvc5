###############################################################################
# Top contributors (to current version):
#   Aina Niemetz
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
#
find_package(Doxygen REQUIRED)

# basic parameters
set(DOXYGEN_INPUT_DIR ${PROJECT_SOURCE_DIR}/include/cvc5)
set(DOXYGEN_OUTPUT_DIR ${CMAKE_CURRENT_BINARY_DIR}/doxygen)
set(DOXYGEN_INPUT "\
${DOXYGEN_INPUT_DIR}/cvc5.h \
${DOXYGEN_INPUT_DIR}/cvc5_kind.h \
${DOXYGEN_INPUT_DIR}/cvc5_types.h \
${PROJECT_SOURCE_DIR}/src/proof/proof_rule.h \
")
set(DOXYGEN_INDEX_FILE ${DOXYGEN_OUTPUT_DIR}/xml/index.xml)

# create doxygen config file
set(DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile.in)
set(DOXYFILE_OUT ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile)
configure_file(${DOXYFILE_IN} ${DOXYFILE_OUT} @ONLY)

# make sure the outpur directory exists
file(MAKE_DIRECTORY ${DOXYGEN_OUTPUT_DIR})

# add the doxygen target
add_custom_command(
  OUTPUT ${DOXYGEN_INDEX_FILE}
  COMMAND Doxygen::doxygen ${DOXYFILE_OUT}
  MAIN_DEPENDENCY ${DOXYFILE_OUT}
  DEPENDS
    ${DOXYGEN_INPUT_DIR}/cvc5.h
    ${DOXYGEN_INPUT_DIR}/cvc5_kind.h
    ${DOXYGEN_INPUT_DIR}/cvc5_types.h
    ${PROJECT_SOURCE_DIR}/src/proof/proof_rule.h
  COMMENT "Generating doxygen API docs"
)
add_custom_target(docs-cpp DEPENDS ${DOXYGEN_INDEX_FILE})

# tell parent scope where to find the output xml
set(CPP_DOXYGEN_XML_DIR
    "${DOXYGEN_OUTPUT_DIR}/xml"
    PARENT_SCOPE
)
