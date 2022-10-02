###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find Murxla
# Murxla_FOUND - system has Murxla
##

include(ExternalProject)

set(Murxla_COMMIT "9ba2583")

add_custom_target(install-for-murxla
  COMMAND DESTDIR=murxla-install ${CMAKE_MAKE_PROGRAM} install
  DEPENDS cvc5-bin
)

ExternalProject_Add(
  Murxla-EP
  EXCLUDE_FROM_ALL ON
  ${COMMON_EP_CONFIG}
  URL https://github.com/murxla/murxla/archive/${Murxla_COMMIT}.tar.gz
  URL_HASH SHA1=176e325344a94250c4f4f6df3a9d2d01d6529a26
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
  COMMAND echo "  LD_LIBRARY_PATH=${CMAKE_BINARY_DIR}/murxla-install/usr/local/lib/ ${MURXLA_BINARY} -t 1 -d --cvc5"
  COMMAND echo "Convert traces to SMT-LIB as follows:"
  COMMAND echo "  LD_LIBRARY_PATH=${CMAKE_BINARY_DIR}/murxla-install/usr/local/lib/ ${MURXLA_BINARY} --smt2 -u \\<filename\\>"
  DEPENDS Murxla-EP
)
