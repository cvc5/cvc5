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
# Normaliz - target for the Normaliz library
# Normaliz_FOUND - Normaliz was found
# Normaliz_FOUND_SYSTEM - system has Normaliz lib
# Normaliz_INCLUDE_DIR - the Normaliz include directory
# Normaliz_LIBRARIES - Libraries needed to use Normaliz
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
  # determine whether to use downloaded GMP
  set(Normaliz_WITH_GMP)
  if(NOT GMP_FOUND_SYSTEM)
    set(Normaliz_WITH_GMP "--with-gmp=<INSTALL_DIR>")
  endif()

  check_ep_downloaded("Normaliz-EP")
  if(NOT Normaliz-EP_DOWNLOADED)
    check_auto_download("Normaliz" "")
  endif()

  include(ExternalProject)

  set(Normaliz_INCLUDE_DIR "${DEPS_BASE}/include/")

  # On Windows, libtool cannot build a shared C++ library with clang: it links
  # the DLL with -nostdlib, which drops clang's compiler-rt builtins (e.g.
  # __chkstk_ms), and mingw's order-sensitive linker then cannot resolve them.
  # Build Normaliz statically instead and let it be absorbed into libcvc5
  # (cvc5's own link goes through the clang driver, which places compiler-rt
  # correctly). Normaliz is compiled with --with-pic, so this is safe.
  if(CMAKE_SYSTEM_NAME STREQUAL "Windows")
    set(Normaliz_STATIC_BUILD TRUE)
    # The msys2 CLANG64 toolchain provides no gcc/g++, so without explicit
    # CC/CXX Normaliz's configure falls back to whatever gcc is on PATH
    # (e.g. the GitHub runner's stock MinGW), which neither finds the msys2
    # GMP headers nor matches the libc++ ABI of the rest of the build.
    set(CONFIGURE_ENV ${CONFIGURE_ENV} ${CMAKE_COMMAND} -E env
      "CC=${CMAKE_C_COMPILER}" "CXX=${CMAKE_CXX_COMPILER}")
  else()
    set(Normaliz_STATIC_BUILD FALSE)
  endif()

  if(BUILD_SHARED_LIBS AND NOT Normaliz_STATIC_BUILD)
    set(LINK_OPTS --enable-shared --disable-static)
    set(Normaliz_LIBRARIES "${DEPS_BASE}/lib/libnormaliz${CMAKE_SHARED_LIBRARY_SUFFIX}")
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

  set(Normaliz_VERSION "3.11.1")
  set(Normaliz_CHECKSUM "9a00d590f0fdcad847e2189696d2842d97ed896ed36c22421874a364047f76e8")

  # The build is in-source (BUILD_IN_SOURCE), so the working directory is the
  # source dir. On Windows ${SHELL} is the sh interpreter needed to run the
  # autotools configure (CreateProcess cannot exec a shell script); elsewhere
  # it is empty. We invoke ./configure by its relative name because autoconf
  # 2.71's auxiliary-directory detection mishandles an absolute Windows path
  # passed as $0 (same approach as FindCoCoA).
  set(Normaliz_BUILD_COMMAND "")
  set(Normaliz_INSTALL_COMMAND "")
  if(Normaliz_STATIC_BUILD)
    # CMake's tarball extraction can leave Makefile.am newer than the shipped
    # Makefile.in, which makes make try to regenerate it with automake (not
    # installed). Neutralise the maintainer regeneration tools so the shipped
    # generated files are used as-is.
    set(Normaliz_NO_REGEN AUTOMAKE=: AUTOCONF=: AUTOHEADER=: ACLOCAL=: MAKEINFO=:)
    # For a self-contained cvc5 (BUILD_SHARED_LIBS OFF), also link the standalone
    # normaliz tool statically (-all-static) so the installed normaliz.exe carries
    # no libc++/libgmp DLL dependencies, matching the static cvc5.exe. This only
    # affects Normaliz's own programs; the libnormaliz.a that cvc5 consumes is an
    # archive and is unaffected.
    set(Normaliz_EXE_LDFLAGS "")
    if(NOT BUILD_SHARED_LIBS)
      set(Normaliz_EXE_LDFLAGS LDFLAGS=-all-static)
    endif()
    set(Normaliz_BUILD_COMMAND BUILD_COMMAND make ${Normaliz_NO_REGEN} ${Normaliz_EXE_LDFLAGS})
    set(Normaliz_INSTALL_COMMAND INSTALL_COMMAND make install ${Normaliz_NO_REGEN} ${Normaliz_EXE_LDFLAGS})
  endif()

  ExternalProject_Add(
    Normaliz-EP
    ${COMMON_EP_CONFIG}
    URL https://github.com/Normaliz/Normaliz/releases/download/v${Normaliz_VERSION}/normaliz-${Normaliz_VERSION}.tar.gz
    URL_HASH SHA256=${Normaliz_CHECKSUM}
    BUILD_IN_SOURCE YES

    CONFIGURE_COMMAND
      ${CONFIGURE_ENV} ${SHELL} ./configure
        --prefix=<INSTALL_DIR> ${LINK_OPTS} --with-pic ${Normaliz_WITH_GMP}
        ${CONFIGURE_OPTS} --without-cocoalib --without-flint --without-hashlibrary
        --without-nauty --without-e-antic --disable-openmp
    ${Normaliz_BUILD_COMMAND}
    ${Normaliz_INSTALL_COMMAND}
    BUILD_BYPRODUCTS ${Normaliz_LIBRARIES}
  )
  add_dependencies(Normaliz-EP GMP)
endif()

set(Normaliz_FOUND TRUE)

# On Windows Normaliz is always built statically (see above) and linked into
# libcvc5, so import it as a static library there regardless of BUILD_SHARED_LIBS.
if(BUILD_SHARED_LIBS AND NOT CMAKE_SYSTEM_NAME STREQUAL "Windows")
  add_library(Normaliz SHARED IMPORTED GLOBAL)
else()
  add_library(Normaliz STATIC IMPORTED GLOBAL)
endif()
set_target_properties(Normaliz PROPERTIES
  IMPORTED_LOCATION "${Normaliz_LIBRARIES}"
  INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${Normaliz_INCLUDE_DIR}"
)
target_link_libraries(Normaliz INTERFACE GMPXX)

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
