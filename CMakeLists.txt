cmake_minimum_required (VERSION 3.0.1)

#-----------------------------------------------------------------------------#

project(cvc4)

# Major component of the version of CVC4.
set(CVC4_MAJOR 1)
# Minor component of the version of CVC4.
set(CVC4_MINOR 7)
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

# Shared library versioning. Increment SOVERSION for every new CVC4 release.
set(CVC4_VERSION "${CVC4_MAJOR}.${CVC4_MINOR}.${CVC4_RELEASE}")
set(CVC4_SOVERSION 5)

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
  if(CMAKE_C_FLAGS)
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${flag}")
  else()
    set(CMAKE_C_FLAGS "${flag}")
  endif()
  message(STATUS "Configuring with C flag '${flag}'")
endmacro()

macro(add_cxx_flag flag)
  if(CMAKE_CXX_FLAGS)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flag}")
  else()
    set(CMAKE_CXX_FLAGS "${flag}")
  endif()
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

# Collect all libraries that must be linked against libcvc4. These will be
# actually linked in src/CMakeLists.txt with target_link_libaries(...).
macro(libcvc4_link_libraries library)
  set(LIBCVC4_LIBRARIES ${LIBCVC4_LIBRARIES} ${library})
endmacro()

# Collect all include directories that are required for libcvc4. These will be
# actually included in src/CMakeLists.txt with target_include_directories(...).
macro(libcvc4_include_directories dirs)
  set(LIBCVC4_INCLUDES ${LIBCVC4_INCLUDES} ${dirs})
endmacro()

# CVC4 Boolean options are three-valued to detect if an option was set by the
# user. The available values are: IGNORE (default), ON, OFF
# Default options do not override options that were set by the user, i.e.,
# cvc4_set_option only sets an option if it's value is still IGNORE.
# This e.g., allows the user to disable proofs for debug builds (where proofs
# are enabled by default).
macro(cvc4_option var description)
  set(${var} IGNORE CACHE STRING "${description}")
  # Provide drop down menu options in cmake-gui
  set_property(CACHE ${var} PROPERTY STRINGS IGNORE ON OFF)
endmacro()

# Only set option if the user did not set an option.
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
option(ENABLE_COVERAGE           "Enable support for gcov coverage testing")
option(ENABLE_PROFILING          "Enable support for gprof profiling")

# Optional dependencies
option(USE_ABC                   "Use ABC for AIG bit-blasting")
option(USE_CADICAL               "Use CaDiCaL SAT solver")
option(USE_CLN                   "Use CLN instead of GMP")
option(USE_CRYPTOMINISAT         "Use CryptoMiniSat SAT solver")
option(USE_GLPK                  "Use GLPK simplex solver")
option(USE_LFSC                  "Use LFSC proof checker")
option(USE_READLINE              "Use readline for better interactive support")
option(USE_SYMFPU                "Use SymFPU for floating point support")

# Custom install directories for dependencies
# If no directory is provided by the user, we first check if the dependency was
# installed via the corresponding contrib/get-* script and if not found, we
# check the intalled system version. If the user provides a directory we
# immediately fail if the dependency was not found at the specified location.
set(ABC_DIR           "" CACHE STRING "Set ABC install directory")
set(ANTLR_DIR         "" CACHE STRING "Set ANTLR3 install directory")
set(CADICAL_DIR       "" CACHE STRING "Set CaDiCaL install directory")
set(CRYPTOMINISAT_DIR "" CACHE STRING "Set CryptoMiniSat install directory")
set(GLPK_DIR          "" CACHE STRING "Set GLPK install directory")
set(GMP_DIR           "" CACHE STRING "Set GMP install directory")
set(LFSC_DIR          "" CACHE STRING "Set LFSC install directory")
set(SYMFPU_DIR        "" CACHE STRING "Set SymFPU install directory")

# Supported language bindings
option(BUILD_BINDINGS_JAVA       "Build Java bindings" OFF)
option(BUILD_BINDINGS_PYTHON     "Build Python bindings" OFF)

# All bindings: c,java,csharp,perl,php,python,ruby,tcl,ocaml


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
# Option defaults (three-valued options (cvc4_option(...)))

cvc4_set_option(ENABLE_PORTFOLIO OFF)
cvc4_set_option(ENABLE_SHARED ON)
cvc4_set_option(ENABLE_VALGRIND OFF)

#-----------------------------------------------------------------------------#

# This needs to be set before any find_package(...) command since we want to
# search for static libraries with suffix .a.
if(NOT ENABLE_SHARED)
  set(CMAKE_FIND_LIBRARY_SUFFIXES ".a")
  set(CMAKE_EXE_LINKER_FLAGS "-static")
  set(BUILD_SHARED_LIBS OFF)
endif()

find_package(PythonInterp REQUIRED)

set(ANTLR_HOME ${ANTLR_DIR})
find_package(ANTLR REQUIRED)

set(GMP_HOME ${GMP_DIR})
find_package(GMP REQUIRED)
libcvc4_link_libraries(${GMP_LIBRARIES})
libcvc4_include_directories(${GMP_INCLUDE_DIR})


#-----------------------------------------------------------------------------#
# Enable the ctest testing framework

enable_testing()

#-----------------------------------------------------------------------------#

if(BUILD_BINDINGS_JAVA OR BUILD_BINDINGS_PYTHON)
  set(BUILD_BINDINGS TRUE)
endif()

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
  setup_target_for_coverage_lcov(
    NAME coverage
    EXECUTABLE ctest $(ARGS)
    DEPENDENCIES cvc4-bin)
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
  find_package(Boost 1.50.0 REQUIRED COMPONENTS thread)
  # Disable CLN for portfolio builds since it is not thread safe (uses an
  # unlocked hash table internally).
  set(USE_CLN OFF)
  set(THREADS_PREFER_PTHREAD_FLAG ON)
  find_package(Threads REQUIRED)
  if(THREADS_HAVE_PTHREAD_ARG)
    add_c_cxx_flag(-pthread)
  endif()
  add_definitions(-DCVC4_PORTFOLIO)
  set(BOOST_HAS_THREAD_ATTR 1)
endif()

if(ENABLE_PROFILING)
  add_definitions(-DCVC4_PROFILING)
  add_check_c_cxx_flag("-pg")
endif()

if(ENABLE_PROOFS)
  set(RUN_REGRESSION_ARGS ${RUN_REGRESSION_ARGS} --enable-proof)
  add_definitions(-DCVC4_PROOF)
  set(CVC4_PROOF 1)
  libcvc4_link_libraries(signatures)
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

if(USE_ABC)
  set(ABC_HOME "${ABC_DIR}")
  find_package(ABC REQUIRED)
  libcvc4_link_libraries(${ABC_LIBRARIES})
  libcvc4_include_directories(${ABC_INCLUDE_DIR})
  add_definitions(-DCVC4_USE_ABC ${ABC_ARCH_FLAGS})
endif()

if(USE_CADICAL)
  set(CaDiCaL_HOME ${CADICAL_DIR})
  find_package(CaDiCaL REQUIRED)
  libcvc4_link_libraries(${CaDiCaL_LIBRARIES})
  libcvc4_include_directories(${CaDiCaL_INCLUDE_DIR})
  add_definitions(-DCVC4_USE_CADICAL)
endif()

if(USE_CLN)
  set(GPL_LIBS "${GPL_LIBS} cln")
  find_package(CLN 1.2.2 REQUIRED)
  libcvc4_link_libraries(${CLN_LIBRARIES})
  libcvc4_include_directories(${CLN_INCLUDE_DIR})
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
  set(CryptoMiniSat_HOME ${CRYPTOMINISAT_DIR})
  find_package(CryptoMiniSat REQUIRED)
  libcvc4_link_libraries(${CryptoMiniSat_LIBRARIES})
  libcvc4_include_directories(${CryptoMiniSat_INCLUDE_DIR})
  add_definitions(-DCVC4_USE_CRYPTOMINISAT)
endif()

if(USE_GLPK)
  set(GPL_LIBS "${GPL_LIBS} glpk")
  set(GLPK_HOME ${GLPK_DIR})
  find_package(GLPK REQUIRED)
  libcvc4_link_libraries(${GLPK_LIBRARIES})
  libcvc4_include_directories(${GLPK_INCLUDE_DIR})
  add_definitions(-DCVC4_USE_GLPK)
endif()

if(USE_LFSC)
  set(RUN_REGRESSION_ARGS ${RUN_REGRESSION_ARGS} --with-lfsc)
  set(LFSC_HOME ${LFSC_DIR})
  find_package(LFSC REQUIRED)
  libcvc4_link_libraries(${LFSC_LIBRARIES})
  libcvc4_include_directories(${LFSC_INCLUDE_DIR})
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
  endif()
endif()

if(USE_SYMFPU)
  set(SymFPU_HOME ${SYMFPU_DIR})
  find_package(SymFPU REQUIRED)
  libcvc4_include_directories(${SymFPU_INCLUDE_DIR})
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

# Defined if using the CLN multi-precision arithmetic library.
set(CVC4_CLN_IMP ${CVC4_USE_CLN_IMP})
# Defined if using the GMP multi-precision arithmetic library.
set(CVC4_GMP_IMP ${CVC4_USE_GMP_IMP})

configure_file(cvc4autoconfig.new.h.in cvc4autoconfig.h)
include_directories(${CMAKE_CURRENT_BINARY_DIR})

#-----------------------------------------------------------------------------#

add_subdirectory(doc)
add_subdirectory(src)
if(BUILD_BINDINGS)
  add_subdirectory(src/bindings)
endif()
if(BUILD_BINDINGS_JAVA)
  add_subdirectory(test/java)
endif()
add_subdirectory(test/regress)
add_subdirectory(test/system)
if(ENABLE_UNIT_TESTING)
	add_subdirectory(test/unit)
endif()

if(ENABLE_PROOFS)
  add_subdirectory(proofs/signatures)
endif()

#-----------------------------------------------------------------------------#
# Print build configuration

if(CVC4_BUILD_PROFILE_PRODUCTION)
  set(CVC4_BUILD_PROFILE_STRING "production")
elseif(CVC4_BUILD_PROFILE_DEBUG)
  set(CVC4_BUILD_PROFILE_STRING "debug")
elseif(CVC4_BUILD_PROFILE_TESTING)
  set(CVC4_BUILD_PROFILE_STRING "testing")
elseif(CVC4_BUILD_PROFILE_COMPETITION)
  set(CVC4_BUILD_PROFILE_STRING "competition")
endif()

# Get all definitions added via add_definitions to print it below
get_directory_property(CVC4_DEFINITIONS COMPILE_DEFINITIONS)
string(REPLACE ";" " " CVC4_DEFINITIONS "${CVC4_DEFINITIONS}")

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
message("Shared libs       : ${ENABLE_SHARED}")
#message("Static binary: ${enable_static_binary}")
#message("Compat lib   : ${CVC4_BUILD_LIBCOMPAT}")
#message("Bindings     : ${bindings_to_be_built}")
#message("")
#message("Multithreaded: ${support_multithreaded}")
message("Portfolio         : ${ENABLE_PORTFOLIO}")
message("")
message("ABC               : ${USE_ABC}")
message("CaDiCaL           : ${USE_CADICAL}")
message("CryptoMiniSat     : ${USE_CRYPTOMINISAT}")
message("GLPK              : ${USE_GLPK}")
message("LFSC              : ${USE_LFSC}")
if(CVC4_USE_CLN_IMP)
  message("MP library        : cln")
else()
  message("MP library        : gmp")
endif()
message("Readline          : ${USE_READLINE}")
message("SymFPU            : ${USE_SYMFPU}")
message("")
message("CPPLAGS (-D...)   : ${CVC4_DEFINITIONS}")
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
message("Install prefix    : ${CMAKE_INSTALL_PREFIX}")
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
