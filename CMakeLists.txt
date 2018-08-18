cmake_minimum_required (VERSION 3.0.1)

#-----------------------------------------------------------------------------#

project(cvc4)

# Major component of the version of CVC4.
set(CVC4_MAJOR 1)
# Minor component of the version of CVC4.
set(CVC4_MINOR 6)
# Release component of the version of CVC4.
set(CVC4_RELEASE 0)
# Extraversion component of the version of CVC4.
set(CVC4_EXTRAVERSION "-prerelease")

# Full release string for CVC4.
if(CVC4_RELEASE)
  set(CVC4_RELEASE_STRING "${CVC4_MAJOR}.${CVC4_MINOR}.${CVC4_RELEASE}${CVC4_EXTRAVERSION}")
else()
  set(CVC4_RELEASE_STRING "${CVC4_MAJOR}.${CVC4_MINOR}${CVC4_EXTRAVERSION}")
endif()

# Define to the full name of this package.
set(PACKAGE_NAME "${PROJECT_NAME}")

#### These defines are only use in autotools make files, will likely be 
#### replaced with corresponding CPack stuff
## Define to the full name and version of this package.
#set(PACKAGE_STRING "${PROJECT_NAME} ${CVC4_RELEASE_STRING}")
## Define to the one symbol short name of this package.
#set(PACKAGE_TARNAME "${PROJECT_NAME}")
## Define to the home page for this package.
#set(PACKAGE_URL "")
## Define to the version of this package.
#set(PACKAGE_VERSION "${CVC4_RELEASE_STRING}")
## Define to the address where bug reports for this package should be sent.
#set(PACKAGE_BUGREPORT "cvc4-bugs@cs.stanford.edu")

#-----------------------------------------------------------------------------#

set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)
set(CMAKE_C_STANDARD 99)
set(CMAKE_CXX_STANDARD 11)

#-----------------------------------------------------------------------------#
# Macros

include(CheckCCompilerFlag)
include(CheckCXXCompilerFlag)

macro(add_c_flag flag)
  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${flag}")
  message(STATUS "Configuring with C flag '${flag}'")
endmacro()

macro(add_cxx_flag flag)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flag}")
  message(STATUS "Configuring with CXX flag '${flag}'")
endmacro()

macro(add_c_cxx_flag flag)
  add_c_flag(${flag})
  add_cxx_flag(${flag})
endmacro()

macro(add_check_c_flag flag)
  string(REGEX REPLACE "[-=]" "_" flagname ${flag})
  check_c_compiler_flag("${flag}" HAVE_FLAG${flagname})
  if(HAVE_FLAG${flagname})
    add_c_flag(${flag})
  endif()
endmacro()

macro(add_check_cxx_flag flag)
  string(REGEX REPLACE "[-=]" "_" flagname ${flag})
  check_cxx_compiler_flag("${flag}" HAVE_FLAG${flagname})
  if(HAVE_FLAG${flagname})
    add_cxx_flag(${flag})
  endif()
endmacro()

macro(add_check_c_cxx_flag flag)
  add_check_c_flag(${flag})
  add_check_cxx_flag(${flag})
endmacro()

macro(add_required_cxx_flag flag)
  string(REGEX REPLACE "[-=]" "_" flagnamename ${flag})
  check_cxx_compiler_flag("${flag}" HAVE_FLAG${flagname})
  if (NOT HAVE_FLAG${flagname})
    message(FATAL_ERROR "Required compiler flag ${flag} not supported")
  endif()
  add_cxx_flag(${flag})
endmacro()

macro(add_required_c_flag flag)
  string(REGEX REPLACE "[-=]" "_" flagname ${flag})
  check_c_compiler_flag("${flag}" HAVE_FLAG${flagname})
  if (NOT HAVE_FLAG${flagname})
    message(FATAL_ERROR "Required compiler flag ${flag} not supported")
  endif()
  add_c_flag(${flag})
endmacro()

macro(add_required_c_cxx_flag flag)
  add_required_c_flag(${flag})
  add_required_cxx_flag(${flag})
endmacro()

macro(cvc4_link_library library)
  set(CVC4_LIBRARIES ${CVC4_LIBRARIES} ${library})
endmacro()

macro(cvc4_option var description)
  set(${var} IGNORE CACHE STRING "${description}")
  # Provide drop down menu options in cmake-gui
  set_property(CACHE ${var} PROPERTY STRINGS IGNORE ON OFF)
endmacro()

macro(cvc4_set_option var value)
  if(${var} STREQUAL "IGNORE")
    set(${var} ${value})
  endif()
endmacro()

#-----------------------------------------------------------------------------#
# User options

# License
option(ENABLE_GPL                "Enable GPL dependencies" OFF)

# General build options
# >> 3-valued: INGORE ON OFF, allows to detect if set by user
#              this is only necessary for options set for build types!
cvc4_option(ENABLE_ASAN          "Enable ASAN build")
cvc4_option(ENABLE_ASSERTIONS    "Enable assertions")
cvc4_option(ENABLE_DEBUG_SYMBOLS "Enable debug symbols")
cvc4_option(ENABLE_DUMPING       "Enable dumpin")
cvc4_option(ENABLE_MUZZLE        "Enable silencing CVC4; supress ALL non-result output")
cvc4_option(ENABLE_OPTIMIZED     "Enable optimization")
cvc4_option(ENABLE_PORTFOLIO     "Enable portfolio support")
cvc4_option(ENABLE_PROOFS        "Enable proof support")
cvc4_option(ENABLE_REPLAY        "Enable the replay feature")
cvc4_option(ENABLE_STATISTICS    "Enable statistics")
cvc4_option(ENABLE_TRACING       "Enable tracing")
cvc4_option(ENABLE_UNIT_TESTING  "Enable unit testing")
cvc4_option(ENABLE_VALGRIND      "Enable valgrind instrumentation")
cvc4_option(ENABLE_SHARED        "Build as shared library")
# >> 2-valued: ON OFF, for options where we don't need to detect if set by user
option(ENABLE_COVERAGE           "Enable support for gcov coverage testing" OFF)
option(ENABLE_PROFILING          "Enable support for gprof profiling" OFF)

# Optional dependencies
option(USE_CADICAL               "Use CaDiCaL SAT solver")
option(USE_CLN                   "Use CLN instead of GMP")
option(USE_CRYPTOMINISAT         "Use CryptoMiniSat SAT solver")
option(USE_LFSC                  "Use LFSC proof checker")
option(USE_READLINE              "Use readline for better interactive support" OFF)
option(USE_SYMFPU                "Use SymFPU for floating point support")


#-----------------------------------------------------------------------------#
# Internal cmake variables

set(OPT_LEVEL 3)
set(GPL_LIBS "")

set(BUILD_TYPES Production Debug Testing Competition)

#-----------------------------------------------------------------------------#
# CVC4 build variables

set(CVC4_DEBUG 0)
set(CVC4_BUILD_PROFILE_PRODUCTION 0)
set(CVC4_BUILD_PROFILE_DEBUG 0)
set(CVC4_BUILD_PROFILE_TESTING 0)
set(CVC4_BUILD_PROFILE_COMPETITION 0)
# Whether CVC4 is built with the (optional) GPLed library dependences.
set(CVC4_GPL_DEPS 0)

#-----------------------------------------------------------------------------#

find_package(PythonInterp REQUIRED)
find_package(ANTLR REQUIRED)

find_package(GMP REQUIRED)
cvc4_link_library(${GMP_LIBRARIES})
include_directories(${GMP_INCLUDE_DIR})

#-----------------------------------------------------------------------------#
# Compiler flags

add_check_c_cxx_flag("-O${OPT_LEVEL}")
add_check_c_flag("-fexceptions")
add_check_c_cxx_flag("-Wno-deprecated")
add_check_cxx_flag("-Wsuggest-override")
add_check_cxx_flag("-Wnon-virtual-dtor")

#-----------------------------------------------------------------------------#
# Build types

if(ENABLE_ASAN)
  set(CMAKE_BUILD_TYPE Debug)
endif()

# Set the default build type to Production
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Production CACHE STRING "Options are: ${BUILD_TYPES}" FORCE)
  # Provide drop down menu options in cmake-gui
  set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS ${BUILD_TYPES})
endif()
message(STATUS "Building ${CMAKE_BUILD_TYPE} build")

if(CMAKE_BUILD_TYPE STREQUAL "Debug")
  include(ConfigDebug)
elseif(CMAKE_BUILD_TYPE STREQUAL "Production")
  include(ConfigProduction)
elseif(CMAKE_BUILD_TYPE STREQUAL "Testing")
  include(ConfigTesting)
elseif(CMAKE_BUILD_TYPE STREQUAL "Competition")
  include(ConfigCompetition)
  # enable_static=yes
  #TODO
  # enable_static_binary=yes
  #TODO
endif()

#-----------------------------------------------------------------------------#

if(ENABLE_ASAN)
  set(CMAKE_REQUIRED_LIBRARIES -fsanitize=address)
  add_required_c_cxx_flag("-fsanitize=address")
  unset(CMAKE_REQUIRED_LIBRARIES)
  add_required_c_cxx_flag("-fno-omit-frame-pointer")
  add_check_c_cxx_flag("-fsanitize-recover=address")
endif()

if(ENABLE_ASSERTIONS)
  add_definitions(-DCVC4_ASSERTIONS)
endif()

if(ENABLE_COVERAGE)
  include(CodeCoverage)
  APPEND_COVERAGE_COMPILER_FLAGS()
  add_definitions(-DCVC4_COVERAGE)
  # TODO set_up_target_for_coverage + regression tests
endif()

if(ENABLE_DUMPING)
  add_definitions(-DCVC4_DUMPING)
else()
  add_definitions(-DNDEBUG)
endif()

if(ENABLE_DEBUG_SYMBOLS)
  add_check_c_cxx_flag("-ggdb3")
endif()

if(ENABLE_MUZZLE)
  add_definitions(-DCVC4_MUZZLE)
endif()

if(ENABLE_PORTFOLIO)
  find_package(Boost REQUIRED COMPONENTS thread)
  set(USE_CLN OFF)
  set(THREADS_PREFER_PTHREAD_FLAG ON)
  find_package(Threads REQUIRED)
  if(THREADS_HAVE_PTHREAD_ARG)
    add_c_cxx_flag(-pthread)
  endif()
  add_definitions(-DCVC4_PORTFOLIO)
endif()

if(ENABLE_PROFILING)
  add_definitions(-DCVC4_PROFILING)
  add_check_c_cxx_flag("-pg")
endif()

if(ENABLE_PROOFS)
  set(RUN_REGRESSION_ARGS ${RUN_REGRESSION_ARGS} --enable-proof)
  add_definitions(-DCVC4_PROOF)
  set(CVC4_PROOF 1)
endif()

if(ENABLE_REPLAY)
  add_definitions(-DCVC4_REPLAY)
endif()

if(ENABLE_TRACING)
  add_definitions(-DCVC4_TRACING)
  set(CVC4_TRACING 1)
endif()

if(ENABLE_UNIT_TESTING)
	find_package(CxxTest REQUIRED)
	enable_testing()
  # Force shared libs for unit tests, static libs with unit tests are not
  # working right now.
  set(ENABLE_SHARED ON)
endif()

if(ENABLE_SHARED)
  set(BUILD_SHARED_LIBS ON)
endif()

if(ENABLE_STATISTICS)
  add_definitions(-DCVC4_STATISTICS_ON)
endif()

if(ENABLE_VALGRIND)
  #TODO check if valgrind available
  add_definitions(-DCVC4_VALGRIND)
endif()

if(USE_CADICAL)
  find_package(CaDiCaL REQUIRED)
  cvc4_link_library(${CaDiCaL_LIBRARIES})
  include_directories(${CaDiCaL_INCLUDE_DIR})
  add_definitions(-DCVC4_USE_CADICAL)
endif()

if(USE_CLN)
  set(GPL_LIBS "${GPL_LIBS} cln")
  if(NOT ENABLE_GPL)
    message(FATAL_ERROR
      "Bad configuration detected: BSD-licensed code only, but also requested "
      "GPLed libraries: ${GPL_LIBS}")
  endif()
  find_package(CLN 1.2.2 REQUIRED)
  cvc4_link_library(${CLN_LIBRARIES})
  include_directories(${CLN_INCLUDE_DIR})
  set(CVC4_USE_CLN_IMP 1)
  set(CVC4_USE_GMP_IMP 0)
else()
  set(CVC4_USE_CLN_IMP 0)
  set(CVC4_USE_GMP_IMP 1)
endif()

if(USE_CRYPTOMINISAT)
  # CryptoMiniSat requires pthreads support
  set(THREADS_PREFER_PTHREAD_FLAG ON)
  find_package(Threads REQUIRED)
  if(THREADS_HAVE_PTHREAD_ARG)
    add_c_cxx_flag(-pthread)
  endif()
  find_package(CryptoMiniSat REQUIRED)
  cvc4_link_library(${CryptoMiniSat_LIBRARIES})
  include_directories(${CryptoMiniSat_INCLUDE_DIR})
  add_definitions(-DCVC4_USE_CRYPTOMINISAT)
endif()

if(USE_LFSC)
  set(RUN_REGRESSION_ARGS ${RUN_REGRESSION_ARGS} --with-lfsc)
  find_package(LFSC REQUIRED)
  include_directories(${LFSC_INCLUDE_DIR})
  add_definitions(-DCVC4_USE_LFSC)
  set(CVC4_USE_LFSC 1)
else()
  set(CVC4_USE_LFSC 0)
endif()

if(USE_READLINE)
  find_package(Readline REQUIRED)
  set(HAVE_LIBREADLINE 1)
  if(Readline_COMPENTRY_FUNC_RETURNS_CHARPTR)
    set(READLINE_COMPENTRY_FUNC_RETURNS_CHARP 1)
  else()
    set(READLINE_COMPENTRY_FUNC_RETURNS_CHARP 0)
  endif()
else()
  set(HAVE_LIBREADLINE 0)
endif()

if(USE_SYMFPU)
  find_package(SymFPU REQUIRED)
  include_directories(${SymFPU_INCLUDE_DIR})
  add_definitions(-DCVC4_USE_SYMFPU)
  set(CVC4_USE_SYMFPU 1)
else()
  set(CVC4_USE_SYMFPU 0)
endif()

if(GPL_LIBS)
  if(NOT ENABLE_GPL)
    message(FATAL_ERROR
      "Bad configuration detected: BSD-licensed code only, but also requested "
      "GPLed libraries: ${GPL_LIBS}")
  endif()
  set(CVC4_GPL_DEPS 1)
endif()

#-----------------------------------------------------------------------------#

set(VERSION "1.6.0-prerelease")
string(TIMESTAMP MAN_DATE "%Y-%m-%d")

#-----------------------------------------------------------------------------#

include(GetGitRevisionDescription)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)
git_local_changes(GIT_IS_DIRTY)
if(${GIT_IS_DIRTY} STREQUAL "DIRTY")
  set(GIT_IS_DIRTY "true")
else()
  set(GIT_IS_DIRTY "false")
endif()

execute_process(
  COMMAND "${GIT_EXECUTABLE}" rev-parse --abbrev-ref HEAD
  OUTPUT_VARIABLE GIT_BRANCH
  OUTPUT_STRIP_TRAILING_WHITESPACE
)

#-----------------------------------------------------------------------------#

include(ConfigureCVC4)

# Define to 1 if Boost threading library has support for thread attributes
set(BOOST_HAS_THREAD_ATTR 0)
# Defined if using the CLN multi-precision arithmetic library.
set(CVC4_CLN_IMP ${CVC4_USE_CLN_IMP})
# Defined if using the GMP multi-precision arithmetic library.
set(CVC4_GMP_IMP ${CVC4_USE_GMP_IMP})
## Defined if the requested minimum BOOST version is satisfied
#set(HAVE_BOOST 1)
## Define to 1 if you have <boost/system/error_code.hpp>
#set(HAVE_BOOST_SYSTEM_ERROR_CODE_HPP 1)
## Define to 1 if you have <boost/thread.hpp>
#set(HAVE_BOOST_THREAD_HPP 1)
# Defined to 1 if clock_gettime() is supported by the platform.
set(HAVE_CLOCK_GETTIME 1)
# define if the compiler supports basic C++11 syntax
set(HAVE_CXX11 1)
# Define to 1 if you have the declaration of `optreset', and to 0 if you don't.
set(HAVE_DECL_OPTRESET 0)
## Define to 1 if you have the declaration of `strerror_r', and to 0 if you
## don't.
#set(HAVE_DECL_STRERROR_R 1)
## Define to 1 if you have the <dlfcn.h> header file.
#set(HAVE_DLFCN_H 1)
# Define to 1 if you have the <ext/stdio_filebuf.h> header file.
set(HAVE_EXT_STDIO_FILEBUF_H 1)
# Defined to 1 if ffs() is supported by the platform.
set(HAVE_FFS 1)
# Define to 1 if you have the <getopt.h> header file.
set(HAVE_GETOPT_H 1)
## Define to 1 if you have the <inttypes.h> header file.
#set(HAVE_INTTYPES_H 1)
## Define to 1 if you have the `gmp' library (-lgmp).
#set(HAVE_LIBGMP 1)
## Define to 1 if you have the `profiler' library (-lprofiler).
#set(HAVE_LIBPROFILER 0)
# Define to 1 to use libreadline
#set(HAVE_LIBREADLINE 0)
## Define to 1 if you have the `tcmalloc' library (-ltcmalloc).
#set(HAVE_LIBTCMALLOC 0)
## Define to 1 if you have the <memory.h> header file.
#set(HAVE_MEMORY_H 1)
# Defined to 1 if sigaltstack() is supported by the platform.
set(HAVE_SIGALTSTACK 1)
## Define to 1 if you have the <stdint.h> header file.
#set(HAVE_STDINT_H 1)
## Define to 1 if you have the <stdlib.h> header file.
#set(HAVE_STDLIB_H 1)
# Define to 1 if you have the `strerror_r' function.
set(HAVE_STRERROR_R 1)
## Define to 1 if you have the <strings.h> header file.
#set(HAVE_STRINGS_H 1)
## Define to 1 if you have the <string.h> header file.
#set(HAVE_STRING_H 1)
# Defined to 1 if strtok_r() is supported by the platform.
set(HAVE_STRTOK_R 1)
## Define to 1 if you have the <sys/stat.h> header file.
#set(HAVE_SYS_STAT_H 1)
## Define to 1 if you have the <sys/types.h> header file.
#set(HAVE_SYS_TYPES_H 1)
# Define to 1 if you have the <unistd.h> header file.
set(HAVE_UNISTD_H 1)
## Define to the sub-directory where libtool stores uninstalled libraries.
#set(LT_OBJDIR ".libs/")
## Define to 1 if you have the ANSI C header files.
#set(STDC_HEADERS 1)
# Define to 1 if strerror_r returns char *.
set(STRERROR_R_CHAR_P 1)

configure_file(cvc4autoconfig.new.h.in cvc4autoconfig.h)
include_directories(${CMAKE_CURRENT_BINARY_DIR})

#-----------------------------------------------------------------------------#

add_subdirectory(doc)
add_subdirectory(src)
add_subdirectory(test/java)
add_subdirectory(test/regress)
add_subdirectory(test/system)
if(ENABLE_UNIT_TESTING)
	add_subdirectory(test/unit)
endif()

if(ENABLE_PROOFS)
  add_subdirectory(proofs/signatures)
  cvc4_link_library(signatures)
endif()

#-----------------------------------------------------------------------------#

if(CVC4_BUILD_PROFILE_PRODUCTION)
  set(CVC4_BUILD_PROFILE_STRING "production")
elseif(CVC4_BUILD_PROFILE_DEBUG)
  set(CVC4_BUILD_PROFILE_STRING "debug")
elseif(CVC4_BUILD_PROFILE_TESTING)
  set(CVC4_BUILD_PROFILE_STRING "testing")
elseif(CVC4_BUILD_PROFILE_COMPETITION)
  set(CVC4_BUILD_PROFILE_STRING "competition")
endif()

message("CVC4 ${CVC4_RELEASE_STRING}")
message("")
message("Build profile     : ${CVC4_BUILD_PROFILE_STRING}")
message("Optimized         : ${ENABLE_OPTIMIZED}")
message("Optimization level: ${OPTIMIZATION_LEVEL}")
message("Debug symbols     : ${ENABLE_DEBUG_SYMBOLS}")
message("Proofs            : ${ENABLE_PROOFS}")
message("Statistics        : ${ENABLE_STATISTICS}")
message("Replay            : ${ENABLE_REPLAY}")
message("Assertions        : ${ENABLE_ASSERTIONS}")
message("Tracing           : ${ENABLE_TRACING}")
message("Dumping           : ${ENABLE_DUMPING}")
message("Muzzle            : ${ENABLE_MUZZLE}")
message("")
message("Unit tests        : ${ENABLE_UNIT_TESTING}")
message("Coverage (gcov)   : ${ENABLE_COVERAGE}")
message("Profiling (gprof) : ${ENABLE_PROFILING}")
message("")
#message("Static libs  : ${enable_static}")
if(BUILD_SHARED_LIBS)
	message("Shared libs       : ON")
else()
	message("Shared libs       : OFF")
endif()
#message("Static binary: ${enable_static_binary}")
#message("Compat lib   : ${CVC4_BUILD_LIBCOMPAT}")
#message("Bindings     : ${bindings_to_be_built}")
#message("")
#message("Multithreaded: ${support_multithreaded}")
#message("Portfolio    : ${with_portfolio}")
message("")
#message("ABC          : ${{with_abc}")
message("CaDiCaL           : ${USE_CADICAL}")
message("Cryptominisat     : ${USE_CRYPTOMINISAT}")
#message("GLPK              : ${USE_GLPK}")
message("LFSC              : ${USE_LFSC}")
#message("MP library   : ${mplibrary}")
message("Readline          : ${USE_READLINE}")
message("SymFPU            : ${USE_SYMFPU}")
message("")
#message("CPPFLAGS     : ${CPPFLAGS}")
message("CXXFLAGS          : ${CMAKE_CXX_FLAGS}")
message("CFLAGS            : ${CMAKE_C_FLAGS}")
#message("LIBS         : ${LIBS}")
#message("LDFLAGS      : ${LDFLAGS}")
#message("")
#message("libcvc4 version        : ${{CVC4_LIBRARY_VERSION}")
#message("libcvc4parser version  : ${CVC4_PARSER_LIBRARY_VERSION}")
#message("libcvc4compat version  : ${CVC4_COMPAT_LIBRARY_VERSION_or_nobuild}")
#message("libcvc4bindings version: ${CVC4_BINDINGS_LIBRARY_VERSION_or_nobuild}")
#message("")
#message("Install into : ${prefix}")
message("")

if(GPL_LIBS)
  message(
  "CVC4 license      : GPLv3 (due to optional libraries; see below)"
  "\n"
  "\n"
  "Please note that CVC4 will be built against the following GPLed libraries:"
  "\n"
  "${GPL_LIBS}"
  "\n"
  "As these libraries are covered under the GPLv3, so is this build of CVC4."
  "\n"
  "CVC4 is also available to you under the terms of the (modified) BSD license."
  "\n"
  "If you prefer to license CVC4 under those terms, please configure CVC4 to"
  "\n"
  "disable all optional GPLed library dependences (-DENABLE_BSD_ONLY=ON)."
  )
else()
  message(
  "CVC4 license      : modified BSD"
  "\n"
  "\n"
  "Note that this configuration is NOT built against any GPL'ed libraries, so"
  "\n"
  "it is covered by the (modified) BSD license.  This is, however, not the best"
  "\n"
  "performing configuration of CVC4.  To build against GPL'ed libraries which"
  "\n"
  "improve CVC4's performance, re-configure with '-DENABLE_GPL -DENABLE_BEST'."
  )
endif()

message("")
message("Now just type make, followed by make check or make install.")
message("")
