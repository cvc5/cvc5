###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Mathias Preiner, Gereon Kremer
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

cmake_minimum_required(VERSION 3.12)

#-----------------------------------------------------------------------------#
# Project configuration

project(cvc5)

include(CheckIPOSupported)
include(GNUInstallDirs)
set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)

include(version)

set(CMAKE_C_STANDARD 99)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_VISIBILITY_PRESET hidden)
set(CMAKE_VISIBILITY_INLINES_HIDDEN 1)

# Generate compile_commands.json, which can be used for various code completion
# plugins.
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

#-----------------------------------------------------------------------------#
# Policies

# Required for FindGLPK since it sets CMAKE_REQUIRED_LIBRARIES
if(POLICY CMP0075)
  cmake_policy(SET CMP0075 NEW)
endif()

if(POLICY CMP0135)
  # For `ExternalProject_Add()`, set the timestamp of the files extracted from
  # the downloaded archive to the time of the extraction. This behavior was
  # introduced in CMake 3.23 and is the recommended to make sure that
  # dependencies get rebuilt when the URL changes.
  cmake_policy(SET CMP0135 NEW)
endif()

if(POLICY CMP0079)
  # Allows target_link_libraries() to use targets from other directories.
  # This will prevent issues with INTERFACE_LINK_LIBRARIES, which allows
  # cvc5 to be properly linked as a static library on other CMake projects.
  cmake_policy(SET CMP0079 NEW)
endif()

#-----------------------------------------------------------------------------#
# Tell CMake where to find our dependencies

if(GLPK_DIR)
  list(APPEND CMAKE_PREFIX_PATH "${GLPK_DIR}")
endif()

# By default the contrib/get-* scripts install dependencies to deps/install.
list(APPEND CMAKE_PREFIX_PATH "${PROJECT_SOURCE_DIR}/deps/install")

#-----------------------------------------------------------------------------#

include(Helpers)

#-----------------------------------------------------------------------------#
# User options

# License
option(ENABLE_GPL "Enable GPL dependencies")

# General build options
#
# >> 3-valued: IGNORE ON OFF
#    > allows to detect if set by user (default: IGNORE)
#    > only necessary for options set for build types
option(BUILD_SHARED_LIBS          "Build shared libraries and binary")
cvc5_option(ENABLE_ASAN           "Enable ASAN build")
cvc5_option(ENABLE_UBSAN          "Enable UBSan build")
cvc5_option(ENABLE_TSAN           "Enable TSan build")
cvc5_option(ENABLE_ASSERTIONS     "Enable assertions")
cvc5_option(ENABLE_COMP_INC_TRACK
            "Enable optimizations for incremental SMT-COMP tracks")
cvc5_option(ENABLE_DEBUG_SYMBOLS  "Enable debug symbols")
cvc5_option(ENABLE_MUZZLE         "Suppress ALL non-result output")
cvc5_option(ENABLE_STATISTICS     "Enable statistics")
cvc5_option(ENABLE_TRACING        "Enable tracing")
cvc5_option(ENABLE_UNIT_TESTING   "Enable unit testing")
cvc5_option(ENABLE_VALGRIND       "Enable valgrind instrumentation")
cvc5_option(ENABLE_AUTO_DOWNLOAD  "Enable automatic download of dependencies")
cvc5_option(ENABLE_IPO            "Enable interprocedural optimization")
# >> 2-valued: ON OFF
#    > for options where we don't need to detect if set by user (default: OFF)
option(ENABLE_COVERAGE         "Enable support for gcov coverage testing")
option(ENABLE_DEBUG_CONTEXT_MM "Enable the debug context memory manager")
option(ENABLE_PROFILING        "Enable support for gprof profiling")

# Optional dependencies
#
# >> 2-valued: ON OFF
#    > for options where we don't need to detect if set by user (default: OFF)
option(USE_CLN           "Use CLN instead of GMP")
option(USE_COCOA         "Use CoCoALib for further polynomial operations")
option(USE_CRYPTOMINISAT "Use CryptoMiniSat SAT solver")
option(USE_EDITLINE      "Use Editline for better interactive support")
option(USE_GLPK          "Use GLPK simplex solver")
option(USE_KISSAT        "Use Kissat SAT solver")
option(USE_POLY          "Use LibPoly for polynomial arithmetic")

# Custom install directories for dependencies
# If no directory is provided by the user, we first check if the dependency was
# installed via the corresponding contrib/get-* script and if not found, we
# check the intalled system version. If the user provides a directory we
# immediately fail if the dependency was not found at the specified location.
set(GLPK_DIR          "" CACHE STRING "Set GLPK install directory")

# Prepend binaries with prefix on make install
set(PROGRAM_PREFIX    "" CACHE STRING "Program prefix on make install")

# Supported language bindings based on new C++ API
option(BUILD_BINDINGS_PYTHON "Build Python bindings based on new C++ API ")
option(BUILD_BINDINGS_JAVA "Build Java bindings based on new C++ API ")

# Api documentation
option(BUILD_DOCS "Build Api documentation")

# Link against static system libraries
cvc5_option(STATIC_BINARY "Link against static system libraries \
(enabled by default for static builds)")

# Custom flags for WebAssembly compilation
set(WASM_FLAGS "" CACHE STRING "Link flags for the WebAssembly binary generation")
set(WASM "OFF" CACHE STRING "Use a specific extension for WebAssembly compilation")

# Make sure no other available value will be assigned to this variable
if(NOT(WASM STREQUAL "WASM" OR WASM STREQUAL "JS" OR WASM STREQUAL "HTML" OR WASM STREQUAL "OFF"))
  message(FATAL_ERROR "${WASM} is not a valid wasm flag value.")
endif()

if(WASM STREQUAL "OFF")
  set(WASM_FLAGS "")
  set(CONFIGURE_CMD_WRAPPER "")
# If it's a wasm compilation, but isn't using the right flags
elseif(BUILD_SHARED_LIBS OR NOT(STATIC_BINARY) OR NOT(ENABLE_AUTO_DOWNLOAD))
  message(FATAL_ERROR "Use --static, --static-binary and --auto-download flags for WebAssembly compilation. GMP will not compile with shared libraries.")
else()
  set(CONFIGURE_CMD_WRAPPER emconfigure)
  set(TOOLCHAIN_PREFIX wasm64-unknown-emscripten)
  string(TOLOWER ".${WASM}" WASM_EXTENSION)
  set(CMAKE_EXECUTABLE_SUFFIX ${WASM_EXTENSION})
  string(APPEND CMAKE_EXE_LINKER_FLAGS " ${WASM_FLAGS}")
endif()

#-----------------------------------------------------------------------------#
# Internal cmake variables

set(OPTIMIZATION_LEVEL 3)
set(GPL_LIBS "")

#-----------------------------------------------------------------------------#
# Determine number of threads available, used to configure (default) parallel
# execution of custom test targets (can be overriden with ARGS=-jN).

include(ProcessorCount)
ProcessorCount(CTEST_NTHREADS)
if(CTEST_NTHREADS EQUAL 0)
  set(CTEST_NTHREADS 1)
endif()

#-----------------------------------------------------------------------------#
# Build types

# Note: Module CodeCoverage requires the name of the debug build to conform
#       to cmake standards (first letter uppercase).
set(BUILD_TYPES Production Debug Testing Competition)

if(ENABLE_ASAN OR ENABLE_UBSAN OR ENABLE_TSAN)
  set(CMAKE_BUILD_TYPE Debug)
endif()

# Set the default build type to Production
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE
      Production CACHE STRING "Options are: ${BUILD_TYPES}" FORCE)
  # Provide drop down menu options in cmake-gui
  set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS ${BUILD_TYPES})
endif()

# Check if specified build type is valid.
list(FIND BUILD_TYPES ${CMAKE_BUILD_TYPE} FOUND_BUILD_TYPE)
if(${FOUND_BUILD_TYPE} EQUAL -1)
  message(FATAL_ERROR
    "'${CMAKE_BUILD_TYPE}' is not a valid build type. "
    "Available builds are: ${BUILD_TYPES}")
endif()

message(STATUS "Building ${CMAKE_BUILD_TYPE} build")
include(Config${CMAKE_BUILD_TYPE})

#-----------------------------------------------------------------------------#
# Compiler flags

add_check_c_cxx_flag("-O${OPTIMIZATION_LEVEL}")
add_check_c_cxx_flag("-Wall")
add_check_c_cxx_supression_flag("-Wno-unused-private-field")
add_check_c_flag("-fexceptions")
add_check_cxx_flag("-Wsuggest-override")
add_check_cxx_flag("-Wnon-virtual-dtor")
add_check_c_cxx_flag("-Wimplicit-fallthrough")
add_check_c_cxx_flag("-Wshadow")

# Assume no dynamic initialization of thread-local variables in non-defining
# translation units. This option should result in better performance and works
# around crashing issues with our Windows build.
add_check_cxx_flag("-fno-extern-tls-init")

# Disable -Wclass-memaccess to suppress 'no trivial copy-assignment' in MiniSat
# code.
add_check_cxx_supression_flag("-Wno-class-memaccess")

if (WIN32)
  set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl,--stack,100000000")
endif ()

#-----------------------------------------------------------------------------#
# Use ld.mold if available, otherwise use ld.gold if available

set(USE_EXPLICIT_LINKER_FLAG FALSE)
execute_process(COMMAND ${CMAKE_C_COMPILER}
                -fuse-ld=mold
                -Wl,--version ERROR_QUIET OUTPUT_VARIABLE LD_MOLD_VERSION)
if ("${LD_MOLD_VERSION}" MATCHES "mold")
  set(USE_EXPLICIT_LINKER_FLAG TRUE)
  set(EXPLICIT_LINKER_FLAG " -fuse-ld=mold")
  message(STATUS "Using mold linker.")
else ()
  execute_process(COMMAND ${CMAKE_C_COMPILER}
                  -fuse-ld=gold
                  -Wl,--version ERROR_QUIET OUTPUT_VARIABLE LD_GOLD_VERSION)
  if ("${LD_GOLD_VERSION}" MATCHES "GNU gold")
    set(USE_EXPLICIT_LINKER_FLAG TRUE)
    set(EXPLICIT_LINKER_FLAG " -fuse-ld=gold")
    message(STATUS "Using GNU gold linker.")
  endif ()
endif ()
if (USE_EXPLICIT_LINKER_FLAG)
  string(APPEND CMAKE_EXE_LINKER_FLAGS ${EXPLICIT_LINKER_FLAG})
  string(APPEND CMAKE_SHARED_LINKER_FLAGS ${EXPLICIT_LINKER_FLAG})
  string(APPEND CMAKE_MODULE_LINKER_FLAGS ${EXPLICIT_LINKER_FLAG})
endif ()

#-----------------------------------------------------------------------------#
# Use interprocedural optimization if requested

if(ENABLE_IPO)
  check_ipo_supported(RESULT have_ipo_support)
  if(have_ipo_support)
    set(CMAKE_INTERPROCEDURAL_OPTIMIZATION TRUE)
  else()
    message(STATUS "Interprocedural optimization not supported.")
    set(ENABLE_IPO OFF)
  endif()
endif()

#-----------------------------------------------------------------------------#

# Only enable unit testing if assertions are enabled. Otherwise, unit tests
# that expect AssertionException to be thrown will fail.
if(NOT ENABLE_ASSERTIONS)
  message(STATUS "Disabling unit tests since assertions are disabled.")
  set(ENABLE_UNIT_TESTING OFF)
endif()

#-----------------------------------------------------------------------------#
# Shared/static libraries

# Embed the installation prefix as an RPATH in the executable such that the
# linker can find our libraries (such as libcvc5parser) when executing the
# cvc5 binary. This is for example useful when installing cvc5 with a custom
# prefix on macOS (e.g. when using homebrew in a non-standard directory). If
# we do not set this option, then the linker will not be able to find the
# required libraries when trying to run cvc5.
#
# Also embed the installation prefix of the installed contrib libraries as an
# RPATH. This allows to install a dynamically linked binary that depends on
# dynamically linked libraries. This is dangerous, as the installed binary
# breaks if the contrib library is removed or changes in other ways, we thus
# print a big warning and only allow if installing to a custom installation
# prefix.
#
# More information on RPATH in CMake:
# https://gitlab.kitware.com/cmake/community/wikis/doc/cmake/RPATH-handling
set(CMAKE_INSTALL_RPATH "${CMAKE_INSTALL_PREFIX}/${CMAKE_INSTALL_LIBDIR};${PROJECT_SOURCE_DIR}/deps/install/lib")

# Set visibility to default if unit tests are enabled. If unit tests are
# enabled, we also check if we can execute white box unit tests (some versions
# of Clang have issues with the required flag).
set(ENABLE_WHITEBOX_UNIT_TESTING OFF)
if(ENABLE_UNIT_TESTING)
  set(CMAKE_CXX_VISIBILITY_PRESET default)
  set(CMAKE_VISIBILITY_INLINES_HIDDEN 0)

  # Check if Clang version has the bug that was fixed in
  # https://reviews.llvm.org/D93104
  set(ENABLE_WHITEBOX_UNIT_TESTING ON)
  check_cxx_compiler_flag("-faccess-control" HAVE_CXX_FLAGfaccess_control)
  if(NOT HAVE_CXX_FLAGfaccess_control)
    set(ENABLE_WHITEBOX_UNIT_TESTING OFF)
    message(STATUS "Disabling white box unit tests")
  endif()
endif()

#-----------------------------------------------------------------------------#
# Enable the ctest testing framework

# This needs to be enabled here rather than in subdirectory test in order to
# allow calling ctest from the root build directory.
enable_testing()

#-----------------------------------------------------------------------------#
# Check options, find packages and configure build.

if(BUILD_SHARED_LIBS)
  if (WIN32)
    set(CMAKE_FIND_LIBRARY_SUFFIXES .dll .lib .a)
  else()
    set(CMAKE_FIND_LIBRARY_SUFFIXES .so .dylib .a)
  endif()
else()
  if (WIN32)
    set(CMAKE_FIND_LIBRARY_SUFFIXES .lib .a .dll)
  else()
    set(CMAKE_FIND_LIBRARY_SUFFIXES .a .so .dylib)
  endif()
endif()

if(DEFINED BUILD_BINDINGS_PYTHON_VERSION) 
  find_package(Python ${BUILD_BINDINGS_PYTHON_VERSION} EXACT COMPONENTS Interpreter REQUIRED)
else()
  find_supported_python_version()
endif()

# Some cmake packages are not compatible with the newest version
# of FindPython, introduced in cmake 3.12.
# We define the symbols below to be backward compatible.
# FindPython Interpreter sets Python_EXECUTABLE
if(NOT DEFINED PYTHON_EXECUTABLE) 
  set(PYTHON_EXECUTABLE "${Python_EXECUTABLE}")
endif()

find_package(GMP 6.1 REQUIRED)

if(ENABLE_ASAN)
  # -fsanitize=address requires CMAKE_REQUIRED_FLAGS to be explicitely set,
  # otherwise the -fsanitize=address check will fail while linking.
  set(CMAKE_REQUIRED_FLAGS -fsanitize=address)
  add_required_c_cxx_flag("-fsanitize=address")
  unset(CMAKE_REQUIRED_FLAGS)
  add_required_c_cxx_flag("-fno-omit-frame-pointer")
  add_check_c_cxx_flag("-fsanitize-recover=address")
endif()

if(ENABLE_UBSAN)
  add_required_c_cxx_flag("-fsanitize=undefined")
  add_definitions(-DCVC5_USE_UBSAN)
endif()

if(ENABLE_TSAN)
  # -fsanitize=thread requires CMAKE_REQUIRED_FLAGS to be explicitely set,
  # otherwise the -fsanitize=thread check will fail while linking.
  set(CMAKE_REQUIRED_FLAGS -fsanitize=thread)
  add_required_c_cxx_flag("-fsanitize=thread")
  unset(CMAKE_REQUIRED_FLAGS)
endif()

if(ENABLE_ASSERTIONS)
  add_definitions(-DCVC5_ASSERTIONS)
else()
  add_definitions(-DNDEBUG)
endif()

if(ENABLE_COVERAGE)
  include(CodeCoverage)
  append_coverage_compiler_flags()
  add_definitions(-DCVC5_COVERAGE)
  setup_code_coverage_fastcov(
    NAME coverage
    PATH "${PROJECT_SOURCE_DIR}"
    EXCLUDE "${CMAKE_BINARY_DIR}/deps/*"
    DEPENDENCIES cvc5-bin
  )
endif()

if(ENABLE_DEBUG_CONTEXT_MM)
  add_definitions(-DCVC5_DEBUG_CONTEXT_MEMORY_MANAGER)
endif()

if(ENABLE_DEBUG_SYMBOLS)
  add_check_c_cxx_flag("-ggdb3")
  add_check_c_cxx_flag("-gz")
endif()

if(ENABLE_COMP_INC_TRACK)
  add_definitions(-DCVC5_SMTCOMP_APPLICATION_TRACK)
endif()

if(ENABLE_MUZZLE)
  add_definitions(-DCVC5_MUZZLE)
endif()

if(ENABLE_PROFILING)
  add_definitions(-DCVC5_PROFILING)
  add_check_c_cxx_flag("-pg")
endif()

if(ENABLE_TRACING)
  add_definitions(-DCVC5_TRACING)
endif()

if(ENABLE_STATISTICS)
  add_definitions(-DCVC5_STATISTICS_ON)
endif()

if(ENABLE_VALGRIND)
  find_package(Valgrind REQUIRED)
  add_definitions(-DCVC5_VALGRIND)
endif()

find_package(CaDiCaL REQUIRED)

if(USE_CLN)
  set(GPL_LIBS "${GPL_LIBS} cln")
  find_package(CLN 1.2.2 REQUIRED)
  set(CVC5_USE_CLN_IMP 1)
  set(CVC5_USE_GMP_IMP 0)
else()
  set(CVC5_USE_CLN_IMP 0)
  set(CVC5_USE_GMP_IMP 1)
endif()

if(USE_CRYPTOMINISAT)
  # CryptoMiniSat requires pthreads support
  set(THREADS_PREFER_PTHREAD_FLAG ON)
  find_package(Threads REQUIRED)
  if(THREADS_HAVE_PTHREAD_ARG)
    add_c_cxx_flag(-pthread)
  endif()
  find_package(CryptoMiniSat 5.8 REQUIRED)
  add_definitions(-DCVC5_USE_CRYPTOMINISAT)
endif()

if(USE_GLPK)
  set(GPL_LIBS "${GPL_LIBS} glpk")
  find_package(GLPK REQUIRED)
  add_definitions(-DCVC5_USE_GLPK)
endif()

if(USE_KISSAT)
  find_package(Kissat REQUIRED)
  add_definitions(-DCVC5_USE_KISSAT)
endif()

if(USE_POLY)
  find_package(Poly REQUIRED)
  add_definitions(-DCVC5_USE_POLY)
  set(CVC5_USE_POLY_IMP 1)
else()
  set(CVC5_USE_POLY_IMP 0)
endif()

if(USE_COCOA)
  find_package(CoCoA REQUIRED 0.99711)
  add_definitions(-DCVC5_USE_COCOA)
endif()

if(USE_EDITLINE)
  find_package(Editline REQUIRED)
  set(HAVE_LIBEDITLINE 1)
  if(Editline_COMPENTRY_FUNC_RETURNS_CHARPTR)
    set(EDITLINE_COMPENTRY_FUNC_RETURNS_CHARP 1)
  endif()
endif()

find_package(SymFPU REQUIRED)

if(GPL_LIBS)
  if(NOT ENABLE_GPL)
    message(FATAL_ERROR
      "Bad configuration detected: BSD-licensed code only, but also requested "
      "GPLed libraries: ${GPL_LIBS}")
  endif()
  set(CVC5_GPL_DEPS 1)
endif()

#-----------------------------------------------------------------------------#
# Provide targets to inspect iwyu suggestions

include(IWYU)
include(fuzzing-murxla)

#-----------------------------------------------------------------------------#

include(ConfigureCvc5)
if(BUILD_SHARED_LIBS)
  set(CVC5_STATIC_BUILD OFF)
else()
  set(CVC5_STATIC_BUILD ON)
  if(NOT CMAKE_SYSTEM_NAME STREQUAL "Darwin")
    cvc5_set_option(STATIC_BINARY ON)
  endif()
endif()

#-----------------------------------------------------------------------------#
# Add subdirectories

# Include public headers
include_directories(include)
include_directories(${CMAKE_BINARY_DIR}/include)

# Install public headers
install(DIRECTORY include/cvc5 DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})

add_subdirectory(src)

if(BUILD_BINDINGS_PYTHON AND NOT BUILD_SHARED_LIBS)
  message(STATUS "Python bindings can only be built in a shared build.")
  set(BUILD_BINDINGS_PYTHON OFF)
endif()
if(BUILD_BINDINGS_PYTHON)
  set(BUILD_BINDINGS_PYTHON_VERSION ${Python_VERSION})
  add_subdirectory(src/api/python)
endif()

if(BUILD_BINDINGS_JAVA)
  add_subdirectory(src/api/java)
endif()

if(BUILD_DOCS)
  add_subdirectory(docs)
endif()

add_subdirectory(test)

include(target-graphs)

#-----------------------------------------------------------------------------#
# Package configuration
#
# Export cvc5 targets to support find_package(cvc5) in other cmake projects.

include(CMakePackageConfigHelpers)

# If we install a dynamically linked binary that also uses dynamically used
# libraries from deps/install/lib, we need to be cautious. Changing these
# shared libraries from deps/install/lib most probably breaks the binary.
# We only allow such an installation for custom installation prefixes
# (in the assumption that only reasonably experienced users use this and
# also that custom installation prefixes are not used for longer periods of
# time anyway). Also, we print a big warning with further instructions.
if(BUILD_SHARED_LIBS)
  # Get the libraries that cvc5 links against
  get_target_property(libs cvc5 INTERFACE_LINK_LIBRARIES)
  set(LIBS_SHARED_FROM_DEPS "")
  foreach(lib ${libs})
    # Filter out those that are linked dynamically and come from deps/install
    if(lib MATCHES ".*/deps/install/lib/.*\.so")
      list(APPEND LIBS_SHARED_FROM_DEPS ${lib})
    endif()
  endforeach()
  list(LENGTH LIBS_SHARED_FROM_DEPS list_len)
  # Check if we actually use such "dangerous" libraries
  if(list_len GREATER 0)
    # Print a generic warning
    install(CODE "message(WARNING \"You are installing a dynamically linked \
    binary of cvc5 which may be a problem if you are using any dynamically \
    linked third-party library that you obtained through one of the \
    contrib/get-xxx scripts. The binary uses the rpath mechanism to find these \
    locally, hence executing such a contrib script removing the \
    \\\"deps/install\\\" folder most probably breaks the installed binary! \
    Consider installing the dynamically linked dependencies on your system \
    manually or link cvc5 statically.\")")
    # Print the libraries in question
    foreach(lib ${LIBS_SHARED_FROM_DEPS})
      install(CODE "message(WARNING \"The following library is used by the cvc5 binary: ${lib}\")")
    endforeach()
    # Check if we use a custom installation prefix
    if(CMAKE_INSTALL_PREFIX STREQUAL "/usr/local")
      install(CODE "message(FATAL_ERROR \"To avoid installing a \
      soon-to-be-broken binary, system-wide installation is disabled if the \
      binary depends on locally-built shared libraries.\")")
    else()
      install(CODE "message(WARNING \"You have selected a custom install \
      directory ${CMAKE_INSTALL_PREFIX}, so we expect you understood the \
      previous warning and know what you are doing.\")")
    endif()
  endif()
endif()

install(EXPORT cvc5-targets
  FILE cvc5Targets.cmake
  NAMESPACE cvc5::
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/cvc5)

configure_package_config_file(
  ${CMAKE_SOURCE_DIR}/cmake/cvc5Config.cmake.in
  ${CMAKE_BINARY_DIR}/cmake/cvc5Config.cmake
  INSTALL_DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/cvc5
  PATH_VARS CMAKE_INSTALL_LIBDIR
)

write_basic_package_version_file(
  ${CMAKE_CURRENT_BINARY_DIR}/cvc5ConfigVersion.cmake
  VERSION ${CVC5_VERSION}
  COMPATIBILITY ExactVersion
)

install(FILES
  ${CMAKE_BINARY_DIR}/cmake/cvc5Config.cmake
  ${CMAKE_BINARY_DIR}/cvc5ConfigVersion.cmake
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/cvc5
)


#-----------------------------------------------------------------------------#
# Print build configuration

# Set colors.
if(NOT WIN32)
  string(ASCII 27 Esc)
  set(Green "${Esc}[32m")
  set(Blue "${Esc}[1;34m")
  set(ResetColor "${Esc}[m")
endif()

# Convert build type to lower case.
string(TOLOWER ${CMAKE_BUILD_TYPE} CVC5_BUILD_PROFILE_STRING)

# Get all definitions added via add_definitions.
get_directory_property(CVC5_DEFINITIONS COMPILE_DEFINITIONS)
string(REPLACE ";" " " CVC5_DEFINITIONS "${CVC5_DEFINITIONS}")

message("")
print_info("cvc5 ${CVC5_VERSION}")
message("")
if(ENABLE_COMP_INC_TRACK)
  print_config("Build profile             " "${CVC5_BUILD_PROFILE_STRING} (incremental)")
else()
  print_config("Build profile             " "${CVC5_BUILD_PROFILE_STRING}")
endif()
message("")
print_config("Assertions                " ${ENABLE_ASSERTIONS})
print_config("Debug symbols             " ${ENABLE_DEBUG_SYMBOLS})
print_config("Debug context mem mgr     " ${ENABLE_DEBUG_CONTEXT_MM})
message("")
print_config("Muzzle                    " ${ENABLE_MUZZLE})
print_config("Statistics                " ${ENABLE_STATISTICS})
print_config("Tracing                   " ${ENABLE_TRACING})
message("")
print_config("ASan                      " ${ENABLE_ASAN})
print_config("UBSan                     " ${ENABLE_UBSAN})
print_config("TSan                      " ${ENABLE_TSAN})
print_config("Coverage (gcov)           " ${ENABLE_COVERAGE})
print_config("Profiling (gprof)         " ${ENABLE_PROFILING})
print_config("Unit tests                " ${ENABLE_UNIT_TESTING})
print_config("Valgrind                  " ${ENABLE_VALGRIND})
message("")
print_config("Shared build              " ${BUILD_SHARED_LIBS})
print_config("Python bindings           " ${BUILD_BINDINGS_PYTHON})
print_config("Java bindings             " ${BUILD_BINDINGS_JAVA})
print_config("Interprocedural opt.      " ${ENABLE_IPO})
message("")
print_config("CryptoMiniSat             " ${USE_CRYPTOMINISAT} FOUND_SYSTEM ${CryptoMiniSat_FOUND_SYSTEM})
print_config("GLPK                      " ${USE_GLPK})
print_config("Kissat                    " ${USE_KISSAT} FOUND_SYSTEM ${Kissat_FOUND_SYSTEM})
print_config("LibPoly                   " ${USE_POLY} FOUND_SYSTEM ${Poly_FOUND_SYSTEM})
print_config("CoCoALib                  " ${USE_COCOA} FOUND_SYSTEM ${CoCoA_FOUND_SYSTEM})

if(CVC5_USE_CLN_IMP)
  print_config("MP library                " "cln" FOUND_SYSTEM ${CLN_FOUND_SYSTEM})
else()
  print_config("MP library                " "gmp" FOUND_SYSTEM ${GMP_FOUND_SYSTEM})
endif()
print_config("Editline                  " ${USE_EDITLINE})
message("")
print_config("Api docs                  " ${BUILD_DOCS})
message("")
if(GLPK_DIR)
  print_config("GLPK dir                  " ${GLPK_DIR})
endif()
message("")
print_config("CPPLAGS (-D...)" "${CVC5_DEFINITIONS}")
print_config("CXXFLAGS       " "${CMAKE_CXX_FLAGS}")
print_config("CFLAGS         " "${CMAKE_C_FLAGS}")
print_config("Linker flags   " "${CMAKE_EXE_LINKER_FLAGS}")
message("")
print_config("Install prefix " "${CMAKE_INSTALL_PREFIX}")
message("")

if(GPL_LIBS)
  message(
  "${Blue}cvc5 license: "
  "${Yellow}GPLv3 (due to optional libraries; see below)${ResetColor}"
  "\n"
  "\n"
  "Please note that cvc5 will be built against the following GPLed libraries:"
  "\n"
  "${GPL_LIBS}"
  "\n"
  "As these libraries are covered under the GPLv3, so is this build of cvc5."
  "\n"
  "cvc5 is also available to you under the terms of the (modified) BSD license."
  "\n"
  "If you prefer to license cvc5 under those terms, please configure cvc5 to"
  "\n"
  "disable all optional GPLed library dependencies."
  )
else()
  message(
  "${Blue}cvc5 license:${ResetColor} modified BSD"
  "\n"
  "\n"
  "Note that this configuration is NOT built against any GPL'ed libraries, so"
  "\n"
  "it is covered by the (modified) BSD license.  To build against GPL'ed"
  "\n"
  "libraries which can improve cvc5's performance on arithmetic and bit-vector"
  "\n"
  "logics, use the 'configure.sh' script to re-configure with '--best --gpl'."
  )
endif()

if("${CMAKE_GENERATOR}" STREQUAL "Ninja")
  set(BUILD_COMMAND_NAME "ninja")
else()
  set(BUILD_COMMAND_NAME "make")
endif()

message("")
message("Now just type '${BUILD_COMMAND_NAME}', "
        "followed by '${BUILD_COMMAND_NAME} check' "
        "or '${BUILD_COMMAND_NAME} install'.")
message("")
