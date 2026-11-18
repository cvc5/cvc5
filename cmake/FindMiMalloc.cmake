###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find mimalloc
# MiMalloc_FOUND - found mimalloc (always true, it is built if necessary)
# MiMalloc_OBJECT - the mimalloc object file that overrides malloc and friends
#
# Note that we always build mimalloc ourselves: overriding the system
# allocator requires linking mimalloc's single object file (mimalloc.o) into
# the executable, which installed versions of mimalloc do not reliably
# provide.
##

include(deps-helper)

check_ep_downloaded("MiMalloc-EP")
if(NOT MiMalloc-EP_DOWNLOADED)
  check_auto_download("MiMalloc" "--no-mimalloc")
endif()

include(ExternalProject)

set(MiMalloc_VERSION "2.5.2")
set(MiMalloc_CHECKSUM
    "5cf9d2a10fae5551b764e888a623da411c6c6beb0221b847f83492ab1932bdab")

# mimalloc's own build requires CMake >= 3.18, so instead we compile its
# single-file amalgamation (src/static.c) to the object file that overrides
# malloc and friends, with the definitions and flags mimalloc's build uses for
# that object (target mimalloc-obj, with MI_OVERRIDE=ON in a release build).
# Without MI_MALLOC_OVERRIDE, the object does not define malloc and friends.
set(MiMalloc_CFLAGS
  -O3 -DNDEBUG=1 -DMI_MALLOC_OVERRIDE ${CMAKE_C_COMPILE_OPTIONS_PIC}
  -fvisibility=hidden -ftls-model=initial-exec -fno-builtin-malloc
)
if(APPLE)
  # On macOS, the object overrides malloc through MI_OSX_ZONE. MI_OSX_INTERPOSE
  # only takes effect in mimalloc's shared library, but mimalloc's build sets
  # it for the object as well.
  list(APPEND MiMalloc_CFLAGS -DMI_OSX_ZONE=1 -DMI_OSX_INTERPOSE=1)
  foreach(arch ${CMAKE_OSX_ARCHITECTURES})
    list(APPEND MiMalloc_CFLAGS -arch ${arch})
  endforeach()
  if(CMAKE_OSX_DEPLOYMENT_TARGET)
    list(APPEND MiMalloc_CFLAGS
      -mmacosx-version-min=${CMAKE_OSX_DEPLOYMENT_TARGET})
  endif()
  # The system headers are not necessarily installed at /usr/include on macOS.
  if(CMAKE_OSX_SYSROOT)
    list(APPEND MiMalloc_CFLAGS ${CMAKE_C_SYSROOT_FLAG} ${CMAKE_OSX_SYSROOT})
  endif()
endif()
# Only Clang selects its target with --target. GCC is built for one target.
if(CMAKE_C_COMPILER_TARGET AND CMAKE_C_COMPILER_ID MATCHES "Clang")
  list(APPEND MiMalloc_CFLAGS --target=${CMAKE_C_COMPILER_TARGET})
endif()

ExternalProject_Add(
  MiMalloc-EP
  ${COMMON_EP_CONFIG}
  URL https://github.com/microsoft/mimalloc/archive/refs/tags/v${MiMalloc_VERSION}.tar.gz
  URL_HASH SHA256=${MiMalloc_CHECKSUM}
  CONFIGURE_COMMAND ""
  BUILD_COMMAND ${CMAKE_C_COMPILER} ${MiMalloc_CFLAGS} -I<SOURCE_DIR>/include
                -c <SOURCE_DIR>/src/static.c
                -o <BINARY_DIR>/mimalloc${CMAKE_C_OUTPUT_EXTENSION}
        # Since the flags above are copied by hand, check that the object
        # defines malloc (_malloc on macOS), so that a mismatch fails here
        # instead of silently leaving the system allocator in place. The shell
        # command must not contain ';', which CMake treats as a list separator.
        COMMAND sh -c "${CMAKE_NM} -g -P <BINARY_DIR>/mimalloc${CMAKE_C_OUTPUT_EXTENSION} | grep -Eq '^_?malloc [TW]' || (echo 'mimalloc${CMAKE_C_OUTPUT_EXTENSION} does not define malloc' >&2 && false)"
  INSTALL_COMMAND ${CMAKE_COMMAND} -E copy <BINARY_DIR>/mimalloc${CMAKE_C_OUTPUT_EXTENSION}
                  <INSTALL_DIR>/lib/mimalloc${CMAKE_C_OUTPUT_EXTENSION}
  BUILD_BYPRODUCTS <INSTALL_DIR>/lib/mimalloc${CMAKE_C_OUTPUT_EXTENSION}
)

set(MiMalloc_FOUND TRUE)
set(MiMalloc_OBJECT "${DEPS_BASE}/lib/mimalloc${CMAKE_C_OUTPUT_EXTENSION}")

mark_as_advanced(MiMalloc_FOUND)
mark_as_advanced(MiMalloc_OBJECT)

message(STATUS "Building mimalloc ${MiMalloc_VERSION}: ${MiMalloc_OBJECT}")
