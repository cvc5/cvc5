###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find GMP
# GMP_FOUND - should always be true
# GMP - target for the GMP library
##

include(deps-helper)

find_path(GMP_INCLUDE_DIR NAMES gmp.h gmpxx.h)
find_library(GMP_LIBRARIES NAMES gmp)

set(GMP_FOUND_SYSTEM FALSE)
if(GMP_INCLUDE_DIR AND GMP_LIBRARIES)
  set(GMP_FOUND_SYSTEM TRUE)

  function(getversionpart OUTPUT FILENAME DESC)
    file(STRINGS ${FILENAME} RES REGEX "^#define __GNU_MP_${DESC}[ \\t]+.*")
    string(REGEX MATCH "[0-9]+" RES "${RES}")
    set(${OUTPUT}
        "${RES}"
        PARENT_SCOPE
    )
  endfunction()
  getversionpart(MAJOR "${GMP_INCLUDE_DIR}/gmp.h" "VERSION")
  getversionpart(MINOR "${GMP_INCLUDE_DIR}/gmp.h" "VERSION_MINOR")
  getversionpart(PATCH "${GMP_INCLUDE_DIR}/gmp.h" "VERSION_PATCHLEVEL")
  set(GMP_VERSION
      "${MAJOR}.${MINOR}.${PATCH}"
  )

  check_system_version("GMP")
endif()

if(NOT GMP_FOUND_SYSTEM)
  check_ep_downloaded("GMP-EP")
  if(NOT GMP-EP_DOWNLOADED)
    check_auto_download("GMP" "")
  endif()

  include(ExternalProject)

  set(GMP_VERSION "6.2.1")

  ExternalProject_Add(
    GMP-EP
    ${COMMON_EP_CONFIG}
    URL https://gmplib.org/download/gmp/gmp-${GMP_VERSION}.tar.bz2
    URL_HASH SHA1=2dcf34d4a432dbe6cce1475a835d20fe44f75822
    CONFIGURE_COMMAND
      <SOURCE_DIR>/configure --prefix=<INSTALL_DIR> --enable-cxx --with-pic
      --disable-shared --enable-static --host=${TOOLCHAIN_PREFIX}
    BUILD_BYPRODUCTS <INSTALL_DIR>/lib/libgmp.a
  )

  set(GMP_INCLUDE_DIR "${DEPS_BASE}/include/")
  set(GMP_LIBRARIES "${DEPS_BASE}/lib/libgmp.a")
endif()

set(GMP_FOUND TRUE)

add_library(GMP STATIC IMPORTED GLOBAL)
set_target_properties(GMP PROPERTIES IMPORTED_LOCATION "${GMP_LIBRARIES}")
set_target_properties(
  GMP PROPERTIES INTERFACE_INCLUDE_DIRECTORIES "${GMP_INCLUDE_DIR}"
)

mark_as_advanced(GMP_FOUND)
mark_as_advanced(GMP_FOUND_SYSTEM)
mark_as_advanced(GMP_INCLUDE_DIR)
mark_as_advanced(GMP_LIBRARIES)

if(GMP_FOUND_SYSTEM)
  message(STATUS "Found GMP ${GMP_VERSION}: ${GMP_LIBRARIES}")
else()
  message(STATUS "Building GMP ${GMP_VERSION}: ${GMP_LIBRARIES}")
  add_dependencies(GMP GMP-EP)
endif()
