cmake_minimum_required(VERSION 3.1)

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

# Prepend 'prepand_value' to each element of the list 'in_list'. The result
# is stored in 'out_list'.
function(list_prepend in_list prepand_value out_list)
  foreach(_elem ${${in_list}})
    list(APPEND ${out_list} "${prepand_value}${_elem}")
  endforeach()
  set(${out_list} ${${out_list}} PARENT_SCOPE)
endfunction()

#-----------------------------------------------------------------------------#
# libcvc4 macros

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

# Collect all source files that are required to build libcvc4 in LIBCVC4_SRCS
# or LIBCVC4_GEN_SRCS. If GENERATED is the first argument the sources are
# added to LIBCVC4_GEN_SRCS. All sources are prepended with the absolute
# current path path. CMAKE_CURRENT_BINARY_DIR is prepended
# to generated source files.
macro(libcvc4_add_sources)
  set(_sources ${ARGV})

  # Check if the first argument is GENERATED.
  list(GET _sources 0 _generated)
  if(${_generated} STREQUAL "GENERATED")
    list(REMOVE_AT _sources 0)
    set(_cur_path ${CMAKE_CURRENT_BINARY_DIR})
    set(_append_to LIBCVC4_GEN_SRCS)
  else()
    set(_cur_path ${CMAKE_CURRENT_SOURCE_DIR})
    set(_append_to LIBCVC4_SRCS)
  endif()

  # Prepend source files with current path.
  foreach(_src ${_sources})
    list(APPEND ${_append_to} "${_cur_path}/${_src}")
  endforeach()

  file(RELATIVE_PATH
       _rel_path "${PROJECT_SOURCE_DIR}/src" "${CMAKE_CURRENT_SOURCE_DIR}")

  # Make changes to list ${_append_to} visible to the parent scope if not
  # called from src/.
  # Note: ${_append_to} refers to the variable name whereas ${${_append_to}}
  # refers to the contents of the variable.
  if(_rel_path)
    set(${_append_to} ${${_append_to}} PARENT_SCOPE)
  endif()
endmacro()

#-----------------------------------------------------------------------------#
# User options

# License
option(ENABLE_GPL "Enable GPL dependencies")

# General build options
#
# >> 3-valued: INGORE ON OFF
#    > allows to detect if set by user (default: IGNORE)
#    > only necessary for options set for build types
cvc4_option(ENABLE_ASAN          "Enable ASAN build")
cvc4_option(ENABLE_ASSERTIONS    "Enable assertions")
cvc4_option(ENABLE_DEBUG_SYMBOLS "Enable debug symbols")
cvc4_option(ENABLE_DUMPING       "Enable dumping")
cvc4_option(ENABLE_MUZZLE        "Supress ALL non-result output")
cvc4_option(ENABLE_OPTIMIZED     "Enable optimization")
cvc4_option(ENABLE_PORTFOLIO     "Enable portfolio support")
cvc4_option(ENABLE_PROOFS        "Enable proof support")
cvc4_option(ENABLE_REPLAY        "Enable the replay feature")
cvc4_option(ENABLE_STATISTICS    "Enable statistics")
cvc4_option(ENABLE_TRACING       "Enable tracing")
cvc4_option(ENABLE_UNIT_TESTING  "Enable unit testing")
cvc4_option(ENABLE_VALGRIND      "Enable valgrind instrumentation")
cvc4_option(ENABLE_SHARED        "Build as shared library")
# >> 2-valued: ON OFF
#    > for options where we don't need to detect if set by user (default: OFF)
option(ENABLE_BEST             "Enable dependencies known to give best performance")
option(ENABLE_COVERAGE         "Enable support for gcov coverage testing")
option(ENABLE_DEBUG_CONTEXT_MM "Enable the debug context memory manager")
option(ENABLE_PROFILING        "Enable support for gprof profiling")

# Optional dependencies
#
# >> 3-valued: INGORE ON OFF
#    > allows to detect if set by user (default: IGNORE)
#    > only necessary for options set for ENABLE_BEST
cvc4_option(USE_ABC      "Use ABC for AIG bit-blasting")
cvc4_option(USE_CLN      "Use CLN instead of GMP")
cvc4_option(USE_GLPK     "Use GLPK simplex solver")
cvc4_option(USE_READLINE "Use readline for better interactive support")
# >> 2-valued: ON OFF
#    > for options where we don't need to detect if set by user (default: OFF)
option(USE_CADICAL       "Use CaDiCaL SAT solver")
option(USE_CRYPTOMINISAT "Use CryptoMiniSat SAT solver")
option(USE_LFSC          "Use LFSC proof checker")
option(USE_SYMFPU        "Use SymFPU for floating point support")

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
option(BUILD_BINDINGS_JAVA   "Build Java bindings")
option(BUILD_BINDINGS_PYTHON "Build Python bindings")

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
cvc4_set_option(USE_ABC OFF)
cvc4_set_option(USE_GLPK OFF)
cvc4_set_option(USE_READLINE OFF)

#-----------------------------------------------------------------------------#
# Set options for best configuration

if (ENABLE_BEST)
  cvc4_set_option(USE_ABC ON)
  cvc4_set_option(USE_CLN ON)
  cvc4_set_option(USE_GLPK ON)
  cvc4_set_option(USE_READLINE ON)
endif()

#-----------------------------------------------------------------------------#

# This needs to be set before any find_package(...) command since we want to
# search for static libraries with suffix .a.
if(NOT ENABLE_SHARED)
  set(CMAKE_FIND_LIBRARY_SUFFIXES ".a")
  set(CMAKE_EXE_LINKER_FLAGS "-static")
  set(BUILD_SHARED_LIBS OFF)
endif()

find_package(PythonInterp REQUIRED)

#-----------------------------------------------------------------------------#
# Enable the ctest testing framework

enable_testing()

#-----------------------------------------------------------------------------#

set(GMP_HOME ${GMP_DIR})
find_package(GMP REQUIRED)
libcvc4_link_libraries(${GMP_LIBRARIES})
libcvc4_include_directories(${GMP_INCLUDE_DIR})

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

if(ENABLE_DEBUG_CONTEXT_MM)
  add_definitions(-DCVC4_DEBUG_CONTEXT_MEMORY_MANAGER)
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

# signatures needs to come before src since it adds source files to libcvc4.
if(ENABLE_PROOFS)
  add_subdirectory(proofs/signatures)
endif()

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

# Print configuration of 2/3-valued option 'var' with prefix 'str'
macro(print_config str var)
  if(${var} STREQUAL "ON")
    set(OPT_VAL_STR "on")
  elseif(${var} STREQUAL "OFF")
    set(OPT_VAL_STR "off")
  elseif(${var} STREQUAL "IGNORE")
    set(OPT_VAL_STR "default")
  endif()
  message("${str} ${OPT_VAL_STR}")
endmacro()

message("CVC4 ${CVC4_RELEASE_STRING}")
message("")
message("Build profile        : ${CVC4_BUILD_PROFILE_STRING}")
message("")
print_config("GPL                  :" ENABLE_GPL)
print_config("Best configuration   :" ENABLE_BEST)
print_config("Optimized            :" ENABLE_OPTIMIZED)
print_config("Optimization level   :" OPTIMIZATION_LEVEL)
message("")
print_config("Assertions           :" ENABLE_ASSERTIONS)
print_config("Debug symbols        :" ENABLE_DEBUG_SYMBOLS)
print_config("Debug context mem mgr:" ENABLE_DEBUG_CONTEXT_MM)
message("")
print_config("Dumping              :" ENABLE_DUMPING)
print_config("Muzzle               :" ENABLE_MUZZLE)
print_config("Proofs               :" ENABLE_PROOFS)
print_config("Replay               :" ENABLE_REPLAY)
print_config("Statistics           :" ENABLE_STATISTICS)
print_config("Tracing              :" ENABLE_TRACING)
message("")
print_config("Asan                 :" ENABLE_ASAN)
print_config("Coverage (gcov)      :" ENABLE_COVERAGE)
print_config("Profiling (gprof)    :" ENABLE_PROFILING)
print_config("Unit tests           :" ENABLE_UNIT_TESTING)
print_config("Valgrind             :" ENABLE_VALGRIND)
message("")
print_config("Shared libs          :" ENABLE_SHARED)
print_config("Java bindings        :" BUILD_BINDINGS_JAVA)
print_config("Python bindings      :" BUILD_BINDINGS_PYTHON)
message("")
print_config("Portfolio            :" ENABLE_PORTFOLIO)
message("")
print_config("ABC                  :" USE_ABC)
print_config("CaDiCaL              :" USE_CADICAL)
print_config("CryptoMiniSat        :" USE_CRYPTOMINISAT)
print_config("GLPK                 :" USE_GLPK)
print_config("LFSC                 :" USE_LFSC)

if(CVC4_USE_CLN_IMP)
  message("MP library           : cln")
else()
  message("MP library           : gmp")
endif()
print_config("Readline             :" ${USE_READLINE})
print_config("SymFPU               :" ${USE_SYMFPU})
message("")
if(ABC_DIR)
  message("ABC dir              : ${ABC_DIR}")
endif()
if(ANTLR_DIR)
  message("ANTLR dir            : ${ANTLR_DIR}")
endif()
if(CADICAL_DIR)
  message("CADICAL dir          : ${CADICAL_DIR}")
endif()
if(CRYPTOMINISAT_DIR)
  message("CRYPTOMINISAT dir    : ${CRYPTOMINISAT_DIR}")
endif()
if(GLPK_DIR)
  message("GLPK dir             : ${GLPK_DIR}")
endif()
if(GMP_DIR)
  message("GMP dir              : ${GMP_DIR}")
endif()
if(LFSC_DIR)
  message("LFSC dir              : ${LFSC_DIR}")
endif()
if(SYMFPU_DIR)
  message("SYMFPU dir              : ${SYMFPU_DIR}")
endif()
message("")
message("CPPLAGS (-D...)      : ${CVC4_DEFINITIONS}")
message("CXXFLAGS             : ${CMAKE_CXX_FLAGS}")
message("CFLAGS               : ${CMAKE_C_FLAGS}")
#message("LIBS         : ${LIBS}")
#message("LDFLAGS      : ${LDFLAGS}")
#message("")
#message("libcvc4 version        : ${{CVC4_LIBRARY_VERSION}")
#message("libcvc4parser version  : ${CVC4_PARSER_LIBRARY_VERSION}")
#message("libcvc4compat version  : ${CVC4_COMPAT_LIBRARY_VERSION_or_nobuild}")
#message("libcvc4bindings version: ${CVC4_BINDINGS_LIBRARY_VERSION_or_nobuild}")
#message("")
message("Install prefix       : ${CMAKE_INSTALL_PREFIX}")
message("")

if(GPL_LIBS)
  message(
  "CVC4 license         : GPLv3 (due to optional libraries; see below)"
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
  "CVC4 license         : modified BSD"
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
