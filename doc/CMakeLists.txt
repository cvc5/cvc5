###############################################################################
# Top contributors (to current version):
#   Mathias Preiner, Aina Niemetz
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

#-----------------------------------------------------------------------------#
# Set variables required for the documentation *.in files

string(TIMESTAMP MAN_DATE "%Y-%m-%d")
set(VERSION CVC5_RELEASE_STRING)

#-----------------------------------------------------------------------------#
# Generate files

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/SmtEngine.3cvc_template.in
  ${CMAKE_CURRENT_BINARY_DIR}/SmtEngine.3cvc_template)

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/cvc5.1_template.in
  ${CMAKE_CURRENT_BINARY_DIR}/cvc5.1_template)

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/cvc5.5.in
  ${CMAKE_CURRENT_BINARY_DIR}/cvc5.5)

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/libcvc5.3.in
  ${CMAKE_CURRENT_BINARY_DIR}/libcvc5.3)

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/libcvc5parser.3.in
  ${CMAKE_CURRENT_BINARY_DIR}/libcvc5parser.3)

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/options.3cvc_template.in
  ${CMAKE_CURRENT_BINARY_DIR}/options.3cvc_template)

#-----------------------------------------------------------------------------#
# Install man pages

install(FILES ${CMAKE_CURRENT_BINARY_DIR}/cvc5.1 DESTINATION share/man/man1)
install(FILES ${CMAKE_CURRENT_BINARY_DIR}/cvc5.5 DESTINATION share/man/man5)
install(FILES
        ${CMAKE_CURRENT_BINARY_DIR}/libcvc5.3
        ${CMAKE_CURRENT_BINARY_DIR}/libcvc5parser.3
        ${CMAKE_CURRENT_BINARY_DIR}/options.3cvc
        ${CMAKE_CURRENT_BINARY_DIR}/SmtEngine.3cvc
        DESTINATION share/man/man3)
