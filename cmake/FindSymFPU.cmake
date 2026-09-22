###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find SymFPU
# SymFPU_FOUND - should always be true
# SymFPU - interface target for the SymFPU headers
##

find_path(SymFPU_INCLUDE_DIR NAMES symfpu/core/unpackedFloat.h)

# Minimum supported version. Only used for diagnostics, SymFPU does not ship
# any version information (no version header, no pkg-config file), so we probe
# for an API change instead, see below.
set(SymFPU_FIND_VERSION "1.2.0")

set(SymFPU_FOUND_SYSTEM FALSE)
if(SymFPU_INCLUDE_DIR)
  # Found SymFPU to be installed system-wide. Since SymFPU does not expose its
  # version, check for `symfpu::unpackedFloat<t>::makeOne()`, the only
  # declaration added in SymFPU 1.2.0. Earlier versions, including the tagged
  # 1.1.0 release, compute wrong bit-widths for several floating-point
  # conversions, which makes cvc5 fail with errors like "resulting bit-vector
  # size is too large" or crash (cvc5#12662, cvc5#12958).
  include(CheckCXXSourceCompiles)
  include(CMakePushCheckState)
  # RESET, else we inherit CMAKE_REQUIRED_LIBRARIES from earlier find modules
  # (FindGLPK) and turn a header-only check into a link test.
  cmake_push_check_state(RESET)
  set(CMAKE_REQUIRED_INCLUDES "${SymFPU_INCLUDE_DIR}")
  check_cxx_source_compiles(
    "
    #include <symfpu/core/unpackedFloat.h>

    // Minimal stand-in for a SymFPU traits class, enough to instantiate
    // symfpu::unpackedFloat<> without pulling in a back end. Instantiating
    // the class only instantiates the declarations of its members.
    struct probeBitVector {
      probeBitVector(unsigned);
      unsigned getWidth() const;
    };
    struct probeTraits {
      typedef unsigned bwt;
      typedef unsigned fpt;
      typedef bool prop;
      typedef probeBitVector ubv;
      typedef probeBitVector sbv;
    };

    using probe = decltype(&symfpu::unpackedFloat<probeTraits>::makeOne);

    int main() { return 0; }
    "
    SymFPU_COMPATIBLE_VERSION
  )
  cmake_pop_check_state()

  if(SymFPU_COMPATIBLE_VERSION)
    set(SymFPU_FOUND_SYSTEM TRUE)
  else()
    message(STATUS "System version for SymFPU at ${SymFPU_INCLUDE_DIR} has \
incompatible version: minimum required ${SymFPU_FIND_VERSION}")
  endif()
endif()

if(NOT SymFPU_FOUND_SYSTEM)
  check_ep_downloaded("SymFPU-EP")
  if(NOT SymFPU-EP_DOWNLOADED)
    check_auto_download("SymFPU" "")
  endif()

  include(ExternalProject)
  include(deps-helper)

  set(SymFPU_COMMIT "40bdec00e99f8ea1b96c3dac0a05eed11c541639")
  set(SymFPU_CHECKSUM "ba17877fbf0c851e113fddaab225152f1c0b2044429396b56b2f113832e36ce5")

  ExternalProject_Add(
    SymFPU-EP
    ${COMMON_EP_CONFIG}
    URL https://github.com/martin-cs/symfpu/archive/${SymFPU_COMMIT}.tar.gz
    URL_HASH SHA256=${SymFPU_CHECKSUM}
    CONFIGURE_COMMAND ""
    BUILD_COMMAND ""
    INSTALL_COMMAND ${CMAKE_COMMAND} -E copy_directory <SOURCE_DIR>/core
                    <INSTALL_DIR>/include/symfpu/core
    COMMAND ${CMAKE_COMMAND} -E copy_directory <SOURCE_DIR>/utils
            <INSTALL_DIR>/include/symfpu/utils
  )

  set(SymFPU_INCLUDE_DIR "${DEPS_BASE}/include/")
endif()

set(SymFPU_FOUND TRUE)

add_library(SymFPU INTERFACE IMPORTED GLOBAL)
set_target_properties(
  SymFPU PROPERTIES INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${SymFPU_INCLUDE_DIR}"
)

mark_as_advanced(SymFPU_FOUND)
mark_as_advanced(SymFPU_FOUND_SYSTEM)
mark_as_advanced(SymFPU_INCLUDE_DIR)
mark_as_advanced(SymFPU_COMPATIBLE_VERSION)

if(SymFPU_FOUND_SYSTEM)
  message(STATUS "Found SymFPU: ${SymFPU_INCLUDE_DIR}")
else()
  message(STATUS "Building SymFPU: ${SymFPU_INCLUDE_DIR}")
  add_dependencies(SymFPU SymFPU-EP)
endif()
