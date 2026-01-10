###############################################################################
# Top contributors (to current version):
#   Mudathir Mohamed
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find Normaliz
# Normaliz_FOUND - should always be true
# Normaliz - interface target for the Normaliz headers
##

find_path(Normaliz_INCLUDE_DIR NAMES libnormaliz/libnormaliz.h)

set(Normaliz_FOUND_SYSTEM FALSE)
if(Normaliz_INCLUDE_DIR)
  # Found Normaliz to be installed system-wide
  set(Normaliz_FOUND_SYSTEM TRUE)
endif()

if(NOT Normaliz_FOUND_SYSTEM)
  check_ep_downloaded("Normaliz-EP")
  if(NOT Normaliz-EP_DOWNLOADED)
    check_auto_download("Normaliz" "")
  endif()

  include(ExternalProject)
  include(deps-helper)
                       
  set(Normaliz_COMMIT "32fe03dc62b9dec795a593c180222b2380f7a3ab")                         
  set(Normaliz_CHECKSUM "ab9901476607216e6662c882e735eb4675d0e6529c9aece10a9fd72bc3e18a57")
  
  message(STATUS "Normaliz SOURCE_DIR = ${SOURCE_DIR}")  
  include(ExternalProject)

  ExternalProject_Add(   
    Normaliz-EP     
    URL https://github.com/Normaliz/Normaliz/archive/32fe03dc62b9dec795a593c180222b2380f7a3ab.tar.gz
    URL https://github.com/Normaliz/Normaliz/archive/${Normaliz_COMMIT}.tar.gz
    URL_HASH SHA256=${Normaliz_CHECKSUM}    
    BUILD_IN_SOURCE ON
    BUILD_IN_SOURCE ON

  BUILD_IN_SOURCE ON
    CONFIGURE_COMMAND
      ${CONFIGURE_ENV}
          ${CONFIGURE_CMD_WRAPPER} ${SHELL} <SOURCE_DIR>/configure
          ${LINK_OPTS}
          --prefix=<INSTALL_DIR>
          --with-pic
          --enable-cxx
          ${CONFIGURE_OPTS}
    # BUILD_BYPRODUCTS ${GMP_LIBRARIES}
  )
  set(Normaliz_INCLUDE_DIR "${DEPS_BASE}/include/")
  install(
    DIRECTORY ${DEPS_BASE}/lib/
    TYPE LIB
    FILES_MATCHING PATTERN libnormaliz* PATTERN normaliz*.pc
  )
endif()

set(Normaliz_FOUND TRUE)

add_library(Normaliz INTERFACE IMPORTED GLOBAL)
set_target_properties(
  Normaliz PROPERTIES INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${Normaliz_INCLUDE_DIR}"
)

mark_as_advanced(Normaliz_FOUND)
mark_as_advanced(Normaliz_FOUND_SYSTEM)
mark_as_advanced(Normaliz_INCLUDE_DIR)

if(Normaliz_FOUND_SYSTEM)
  message(STATUS "Found Normaliz: ${Normaliz_INCLUDE_DIR}")
else()
  message(STATUS "Building Normaliz: ${Normaliz_INCLUDE_DIR}")
  add_dependencies(Normaliz Normaliz-EP)
endif()
