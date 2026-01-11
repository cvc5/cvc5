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
# Normaliz - target for the Normaliz library
##

include(deps-helper)

if (NOT BUILD_Normaliz)
  find_path(Normaliz_INCLUDE_DIR NAMES libnormaliz/libnormaliz.h)  
  find_library(Normaliz_LIBRARIES NAMES normaliz)  
endif()

set(Normaliz_FOUND_SYSTEM FALSE)
if(Normaliz_INCLUDE_DIR AND Normaliz_LIBRARIES)
  set(Normaliz_FOUND_SYSTEM TRUE)  
endif()

if(NOT Normaliz_FOUND_SYSTEM)
  check_ep_downloaded("Normaliz-EP")
  if(NOT Normaliz-EP_DOWNLOADED)
    check_auto_download("Normaliz" "")
  endif()

  include(ExternalProject)

  set(Normaliz_INCLUDE_DIR "${DEPS_BASE}/include/")

  set(Normaliz_CFLAGS "")
  set(Normaliz_CXXFLAGS "")

  if(BUILD_SHARED_LIBS)
    set(LINK_OPTS --enable-shared --disable-static)
    if(CMAKE_SYSTEM_NAME STREQUAL "Windows")
      set(Normaliz_LIBRARIES "${DEPS_BASE}/lib/libnormaliz.dll.a")
    else()
      set(Normaliz_LIBRARIES "${DEPS_BASE}/lib/libnormaliz${CMAKE_SHARED_LIBRARY_SUFFIX}")
    endif()
  else()
    set(LINK_OPTS --disable-shared --enable-static)
    set(Normaliz_LIBRARIES "${DEPS_BASE}/lib/libnormaliz.a")
  endif()

  set(CONFIGURE_OPTS "")  

  if(CMAKE_CROSSCOMPILING OR CMAKE_CROSSCOMPILING_MACOS)
    set(CONFIGURE_OPTS
      --host=${TOOLCHAIN_PREFIX}
      --build=${CMAKE_HOST_SYSTEM_PROCESSOR})

    set(CONFIGURE_ENV ${CONFIGURE_ENV} ${CMAKE_COMMAND} -E
      env "CC_FOR_BUILD=cc")
    if (CMAKE_CROSSCOMPILING_MACOS)
      set(CONFIGURE_ENV
        ${CONFIGURE_ENV}
        env "LDFLAGS=-arch ${CMAKE_OSX_ARCHITECTURES}")
      set(Normaliz_CFLAGS "${Normaliz_CFLAGS} --target=${TOOLCHAIN_PREFIX}")
      set(Normaliz_CXXFLAGS "${Normaliz_CXXFLAGS} --target=${TOOLCHAIN_PREFIX}")
    endif()
  else()
    set(CONFIGURE_OPTS --build=${BUILD_TRIPLET}) # Defined in Helpers
  endif()
  set(CONFIGURE_ENV ${CONFIGURE_ENV} env "CXXFLAGS=${Normaliz_CXXFLAGS}" env "CFLAGS=${Normaliz_CFLAGS}")

  set(Normaliz_COMMIT "32fe03dc62b9dec795a593c180222b2380f7a3ab")                         
  set(Normaliz_CHECKSUM "ab9901476607216e6662c882e735eb4675d0e6529c9aece10a9fd72bc3e18a57")
  
  message ("CONFIGURE_ENV: ${CONFIGURE_ENV}")
  message ("CONFIGURE_CMD_WRAPPER: ${CONFIGURE_CMD_WRAPPER}")
  ExternalProject_Add(
    Normaliz-EP
    ${COMMON_EP_CONFIG}
    URL https://github.com/Normaliz/Normaliz/archive/${Normaliz_COMMIT}.tar.gz
    URL_HASH SHA256=${Normaliz_CHECKSUM}          
    PATCH_COMMAND autoreconf -i <SOURCE_DIR>
    CONFIGURE_COMMAND
      ${CONFIGURE_ENV}
          ${CONFIGURE_CMD_WRAPPER} ${SHELL} <SOURCE_DIR>/configure
          ${LINK_OPTS}
          --prefix=<INSTALL_DIR>
          --with-pic
          --enable-cxx
          ${CONFIGURE_OPTS}
    BUILD_BYPRODUCTS ${Normaliz_LIBRARIES}
  )
  ExternalProject_Get_Property(Normaliz-EP SOURCE_DIR)
  message(STATUS "Normaliz SOURCE_DIR = ${SOURCE_DIR}")
endif()

set(Normaliz_FOUND TRUE)


if(BUILD_SHARED_LIBS)
  add_library(Normaliz SHARED IMPORTED GLOBAL)
  if(CMAKE_SYSTEM_NAME STREQUAL "Windows")
    set_target_properties(Normaliz PROPERTIES IMPORTED_IMPLIB "${Normaliz_LIBRARIES}")
  endif()
else()
  add_library(Normaliz STATIC IMPORTED GLOBAL)
endif()
set_target_properties(Normaliz PROPERTIES
  IMPORTED_LOCATION "${Normaliz_LIBRARIES}"
  INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${Normaliz_INCLUDE_DIR}"
)

mark_as_advanced(Normaliz_FOUND)
mark_as_advanced(Normaliz_FOUND_SYSTEM)
mark_as_advanced(Normaliz_INCLUDE_DIR)
mark_as_advanced(Normaliz_LIBRARIES)

if(Normaliz_FOUND_SYSTEM)
  message(STATUS "Found Normaliz: ${Normaliz_LIBRARIES}")
else()
  message(STATUS "Building Normaliz: ${Normaliz_LIBRARIES}")
  add_dependencies(Normaliz Normaliz-EP)
  # Static builds install the Normaliz static libraries.
  # These libraries are required to compile a program that
  # uses the cvc5 static library.
  # On Windows, this installs the import libraries (LIB) and
  # the DLL libraries (BIN)
  install(
    DIRECTORY ${DEPS_BASE}/lib/
    TYPE LIB
    FILES_MATCHING PATTERN libnormaliz* PATTERN normaliz*.pc
  )
  if(BUILD_SHARED_LIBS AND WIN32)
    install(
      DIRECTORY ${DEPS_BASE}/${CMAKE_INSTALL_BINDIR}/
      TYPE BIN
      FILES_MATCHING PATTERN libnormaliz*
    )
  endif()
  if(NOT SKIP_SET_RPATH AND BUILD_SHARED_LIBS AND APPLE)
    install(CODE "
      file(GLOB Normaliz_DYLIBS \"\${CMAKE_INSTALL_PREFIX}/${CMAKE_INSTALL_LIBDIR}/libnormaliz*.dylib\")
      foreach(Normaliz_DYLIB \${Normaliz_DYLIBS})
        execute_process(COMMAND \${CMAKE_COMMAND}
          -DRPATH=@loader_path
          -DINSTALL_NAME_TOOL=${CMAKE_INSTALL_NAME_TOOL}
          -DDYLIB_PATH=\${Normaliz_DYLIB}
          -DDEPS_BASE=${DEPS_BASE}
          -P ${CMAKE_SOURCE_DIR}/cmake/update_rpath_macos.cmake)
      endforeach()
    ")
  endif()
endif()
