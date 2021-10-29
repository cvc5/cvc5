###############################################################################
# Top contributors (to current version):
#   Gereon Kremer
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find Murxla
# Murxla_FOUND - system has Murxla
##

if(NOT IS_DIRECTORY "${CMAKE_BINARY_DIR}/murxla")
  # this is only necessary while the murxla repository is private
  add_custom_target(fuzz-murxla
    COMMAND echo "To enable make fuzz-murxla run"
    COMMAND echo "git clone git@github.com:murxla/murxla.git ${CMAKE_BINARY_DIR}/murxla"
  )
  return()
endif()

include(ExternalProject)

set(Murxla_COMMIT "afc5744766d6aa61ad5b7ea27007666ac7a5aec2")

add_custom_target(install-for-murxla
  COMMAND ${CMAKE_MAKE_PROGRAM} install DESTDIR=murxla-install
  DEPENDS cvc5-bin
)

ExternalProject_Add(
  Murxla-EP
  EXCLUDE_FROM_ALL ON
  ${COMMON_EP_CONFIG}
  #URL https://github.com/murxla/murxla/archive/${Murxla_COMMIT}.tar.gz
  #URL_HASH SHA1=da39a3ee5e6b4b0d3255bfef95601890afd80709
  SOURCE_DIR ${CMAKE_BINARY_DIR}/murxla
  CMAKE_ARGS
    -DCMAKE_PREFIX_PATH=${CMAKE_BINARY_DIR}/murxla-install/usr/local/
    -DENABLE_BITWUZLA=OFF
    -DENABLE_BOOLECTOR=OFF
    -DENABLE_YICES=OFF
  INSTALL_COMMAND
    ${CMAKE_COMMAND} -E copy <BINARY_DIR>/bin/murxla <INSTALL_DIR>/bin/murxla
  DEPENDS install-for-murxla
)
ExternalProject_Get_Property(Murxla-EP BINARY_DIR)
set(MURXLA_BINARY "deps/bin/murxla")

add_custom_target(fuzz-murxla
  COMMAND echo ""
  COMMAND echo "Run Murxla as follows:"
  COMMAND echo "  LD_LIBRARY_PATH=${CMAKE_BINARY_DIR}/murxla-install/usr/local/lib/ ${MURXLA_BINARY} -t 1 --cvc5"
  DEPENDS Murxla-EP
)