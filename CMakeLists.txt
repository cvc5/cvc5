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

set (CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)
set(CMAKE_C_STANDARD 99)
set(CMAKE_CXX_STANDARD 11)

#-----------------------------------------------------------------------------#

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

#-----------------------------------------------------------------------------#

set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
message(STATUS "LIB directory is '${CMAKE_BINARY_DIR}/lib'")
message(STATUS "BIN directory is '${CMAKE_BINARY_DIR}/bin'")

#-----------------------------------------------------------------------------#

set(build_types Debug Production)
if(NOT CMAKE_BUILD_TYPE)
    message(STATUS "No build type set, options are: ${build_types}")
    set(CMAKE_BUILD_TYPE Production CACHE STRING "Options are: ${build_types}" FORCE)
    # Provide drop down menu options in cmake-gui
    set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS ${build_types})
endif()
message(STATUS "Building ${CMAKE_BUILD_TYPE} build")

#-----------------------------------------------------------------------------#

option(ENABLE_DEBUG_SYMBOLS, "Enable debug symbols" OFF)
option(ENABLE_DUMPING        "Enable dumpin" OFF)
option(ENABLE_PROOFS         "Enable proof support" OFF)
option(ENABLE_REPLAY         "Enable the replay feature" OFF)
option(ENABLE_TRACING        "Enable tracing" OFF)
option(ENABLE_STATISTICS     "Enable statistics" OFF)
option(ENABLE_VALGRIND       "Enable valgrind instrumentation" OFF)

option(USE_CADICAL           "Use CaDiCaL SAT solver" OFF)
option(USE_CLN               "Use CLN instead of GMP" OFF)
option(USE_CRYPTOMINISAT     "Use CryptoMiniSat SAT solver" OFF)
option(USE_LFSC              "Use LFSC proof checker" OFF)
option(USE_SYMFPU            "Use SymFPU for floating point support" OFF)

set(OPTIMIZATION_LEVEL 0)

set(CVC4_DEBUG 0)
set(CVC4_BUILD_PROFILE_PRODUCTION 0)
set(CVC4_BUILD_PROFILE_DEBUG 0)
set(CVC4_BUILD_PROFILE_TESTING 0)
set(CVC4_BUILD_PROFILE_COMPETITION 0)


#-----------------------------------------------------------------------------#

find_package(PythonInterp REQUIRED)
find_package(ANTLR REQUIRED)

find_package(GMP REQUIRED)
cvc4_link_library(${GMP_LIBRARIES})
include_directories(${GMP_INCLUDE_DIR})

#-----------------------------------------------------------------------------#

add_check_c_cxx_flag("-O${OPTIMIZATION_LEVEL}")
add_check_c_flag("-fexceptions")
add_check_c_cxx_flag("-Wno-deprecated")
add_check_c_cxx_flag("-Wsuggest-override")
add_check_cxx_flag("-Wnon-virtual-dtor")

set(build_types production debug testing competition)
if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE production CACHE STRING "Options are: ${build_types}" FORCE)
    # Provide drop down menu options in cmake-gui
    set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS ${build_types})
endif()
message(STATUS "Building ${CMAKE_BUILD_TYPE} build")

if(CMAKE_BUILD_TYPE STREQUAL "debug")
  include(ConfigDebug)
elseif(CMAKE_BUILD_TYPE STREQUAL "production")
  include(ConfigProduction)
elseif(CMAKE_BUILD_TYPE STREQUAL "testing")
  include(ConfigTesting)
elseif(CMAKE_BUILD_TYPE STREQUAL "competition")
  include(ConfigCompetition)
  # enable_static=yes
  #TODO
  # enable_static_binary=yes
  #TODO
endif()

#-----------------------------------------------------------------------------#

if(ENABLE_ASSERTIONS)
  add_definitions(-DCVC4_ASSERTIONS)
endif()

if(ENABLE_DUMPING)
  add_definitions(-DCVC4_DUMPING)
endif()

if(ENABLE_DEBUG_SYMBOLS)
  add_check_c_cxx_flag("-ggdb3")
endif()

if(ENABLE_PROOFS)
  #TODO RUN_REGRESSION_ARGS="${RUN_REGRESSION_ARGS:+$RUN_REGRESSION_ARGS }--enable-proof"
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
  find_package(LFSC REQUIRED)
  include_directories(${LFSC_INCLUDE_DIR})
  add_definitions(-DCVC4_USE_LFSC)
  set(CVC4_USE_LFSC 1)
else()
  set(CVC4_USE_LFSC 0)
endif()

if(USE_SYMFPU)
  find_package(SymFPU REQUIRED)
  include_directories(${SymFPU_INCLUDE_DIR})
  add_definitions(-DCVC4_USE_SYMFPU)
  set(CVC4_USE_SYMFPU 1)
else()
  set(CVC4_USE_SYMFPU 0)
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
set(CVC4_CLN_IMP 0)
# Defined if using the GMP multi-precision arithmetic library.
set(CVC4_GMP_IMP 1)
# Whether CVC4 is built with the (optional) GPLed library dependences.
set(CVC4_GPL_DEPS 0)
# Defined if the requested minimum BOOST version is satisfied
set(HAVE_BOOST 1)
# Define to 1 if you have <boost/system/error_code.hpp>
set(HAVE_BOOST_SYSTEM_ERROR_CODE_HPP 1)
# Define to 1 if you have <boost/thread.hpp>
set(HAVE_BOOST_THREAD_HPP 1)
# Defined to 1 if clock_gettime() is supported by the platform.
set(HAVE_CLOCK_GETTIME 1)
# define if the compiler supports basic C++11 syntax
set(HAVE_CXX11 1)
# Define to 1 if you have the declaration of `optreset', and to 0 if you don't.
set(HAVE_DECL_OPTRESET 0)
# Define to 1 if you have the declaration of `strerror_r', and to 0 if you
# don't.
set(HAVE_DECL_STRERROR_R 1)
# Define to 1 if you have the <dlfcn.h> header file.
set(HAVE_DLFCN_H 1)
# Define to 1 if you have the <ext/stdio_filebuf.h> header file.
set(HAVE_EXT_STDIO_FILEBUF_H 1)
# Defined to 1 if ffs() is supported by the platform.
set(HAVE_FFS 1)
# Define to 1 if you have the <getopt.h> header file.
set(HAVE_GETOPT_H 1)
# Define to 1 if you have the <inttypes.h> header file.
set(HAVE_INTTYPES_H 1)
# Define to 1 if you have the `gmp' library (-lgmp).
set(HAVE_LIBGMP 1)
## Define to 1 if you have the `profiler' library (-lprofiler).
#set(HAVE_LIBPROFILER 0)
# Define to 1 to use libreadline
set(HAVE_LIBREADLINE 0)
## Define to 1 if you have the `tcmalloc' library (-ltcmalloc).
#set(HAVE_LIBTCMALLOC 0)
# Define to 1 if you have the <memory.h> header file.
set(HAVE_MEMORY_H 1)
# Defined to 1 if sigaltstack() is supported by the platform.
set(HAVE_SIGALTSTACK 1)
# Define to 1 if you have the <stdint.h> header file.
set(HAVE_STDINT_H 1)
# Define to 1 if you have the <stdlib.h> header file.
set(HAVE_STDLIB_H 1)
# Define to 1 if you have the `strerror_r' function.
set(HAVE_STRERROR_R 1)
# Define to 1 if you have the <strings.h> header file.
set(HAVE_STRINGS_H 1)
# Define to 1 if you have the <string.h> header file.
set(HAVE_STRING_H 1)
# Defined to 1 if strtok_r() is supported by the platform.
set(HAVE_STRTOK_R 1)
# Define to 1 if you have the <sys/stat.h> header file.
set(HAVE_SYS_STAT_H 1)
# Define to 1 if you have the <sys/types.h> header file.
set(HAVE_SYS_TYPES_H 1)
# Define to 1 if you have the <unistd.h> header file.
set(HAVE_UNISTD_H 1)
## Define to the sub-directory where libtool stores uninstalled libraries.
#set(LT_OBJDIR ".libs/")
# Define to 1 if rl_completion_entry_function is declared to return pointer
# to char
set(READLINE_COMPENTRY_FUNC_RETURNS_CHARP 0)
## Define to 1 if you have the ANSI C header files.
#set(STDC_HEADERS 1)
# Define to 1 if strerror_r returns char *.
set(STRERROR_R_CHAR_P 1)

configure_file(cvc4autoconfig.new.h.in cvc4autoconfig.h)
include_directories(${CMAKE_CURRENT_BINARY_DIR})

#-----------------------------------------------------------------------------#

add_subdirectory(doc)
add_subdirectory(src)

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
message("Optimization level: ${OPTIMIZATION_LEVEL}")
message("Debug symbols     : ${ENABLE_DEBUG_SYMBOLS}")
message("Proofs            : ${ENABLE_PROOFS}")
message("Statistics        : ${ENABLE_STATISTICS}")
message("Replay            : ${ENABLE_REPLAY}")
message("Assertions        : ${ENABLE_ASSERTIONS}")
message("Tracing           : ${ENABLE_TRACING}")
message("Dumping           : ${ENABLE_DUMPING}")
#message("Muzzle            : ${ENABLE_MUZZLE}")
#message("")
#message("Unit tests   : ${support_unit_tests}")
#message("gcov support : ${enable_coverage}")
#message("gprof support: ${enable_profiling}")
#message("")
#message("Static libs  : ${enable_static}")
#message("Shared libs  : ${enable_shared}")
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
#message("Readline     : ${with_readline}")
message("SymFPU            : ${USE_SYMFPU}")
message("")
#message("CPPFLAGS     : ${CPPFLAGS}")
message("CXXFLAGS     : ${CMAKE_CXX_FLAGS}")
message("CFLAGS       : ${CMAKE_C_FLAGS}")
#message("LIBS         : ${LIBS}")
#message("LDFLAGS      : ${LDFLAGS}")
#message("")
#message("libcvc4 version        : ${{CVC4_LIBRARY_VERSION}")
#message("libcvc4parser version  : ${CVC4_PARSER_LIBRARY_VERSION}")
#message("libcvc4compat version  : ${CVC4_COMPAT_LIBRARY_VERSION_or_nobuild}")
#message("libcvc4bindings version: ${CVC4_BINDINGS_LIBRARY_VERSION_or_nobuild}")
#message("")
#message("Install into : ${prefix}")
#message("")
#message("CVC4 license : ${license}")
#message("")
#message("${licensewarn}Now just type make, followed by make check or make install, as you like.")
