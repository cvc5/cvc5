###############################################################################
# Top contributors (to current version):
#   Mathias Preiner, Andres Noetzli, Gereon Kremer
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Toolchain file for building for ARM on Ubuntu host.
#
# Use: cmake .. -DCMAKE_TOOLCHAIN_FILE=../cmake/Toolchain-aarch64.cmake
##

if(CMAKE_SYSTEM_NAME STREQUAL "Linux")

  set(CMAKE_SYSTEM_NAME Linux)
  set(CMAKE_SYSTEM_PROCESSOR aarch64)

  set(TOOLCHAIN_PREFIX aarch64-linux-gnu)

  set(CMAKE_C_COMPILER ${TOOLCHAIN_PREFIX}-gcc)
  set(CMAKE_CXX_COMPILER ${TOOLCHAIN_PREFIX}-g++)

  # Set target environment path
  set(CMAKE_FIND_ROOT_PATH /usr/${TOOLCHAIN_PREFIX})

  # Adjust the default behaviour of the find_XXX() commands:
  # search headers and libraries in the target environment, search
  # programs in the host environment
  set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)
  set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
  set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)

elseif(CMAKE_SYSTEM_NAME STREQUAL "Darwin")

  set(CMAKE_SYSTEM_NAME Darwin)
  set(CMAKE_SYSTEM_PROCESSOR arm64)

  set(TOOLCHAIN_PREFIX arm64-apple-darwin)

  set(CMAKE_CROSSCOMPILING_MACOS TRUE)
  set(CMAKE_OSX_ARCHITECTURES arm64 CACHE INTERNAL "")

endif()
