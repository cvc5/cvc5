###############################################################################
# Top contributors (to current version):
#   Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Toolchain file for building for ARM on Ubuntu host.
#
# Use: cmake .. -DCMAKE_TOOLCHAIN_FILE=../cmake/Toolchain-aarch64.cmake
##

SET(CMAKE_SYSTEM_NAME Linux)
SET(CMAKE_SYSTEM_PROCESSOR arm)

set(TOOLCHAIN_PREFIX aarch64-linux-gnu)

SET(CMAKE_C_COMPILER ${TOOLCHAIN_PREFIX}-gcc)
SET(CMAKE_CXX_COMPILER ${TOOLCHAIN_PREFIX}-g++)

# Set target environment path
SET(CMAKE_FIND_ROOT_PATH /usr/${TOOLCHAIN_PREFIX})

# Adjust the default behaviour of the find_XXX() commands:
# search headers and libraries in the target environment, search
# programs in the host environment
set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)
set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY BOTH)
set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE BOTH)
