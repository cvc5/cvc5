cmake_minimum_required(VERSION 3.2)

#-----------------------------------------------------------------------------#
# Project configuration

project(cvc4)

set(CVC4_MAJOR   1) # Major component of the version of CVC4.
set(CVC4_MINOR   8) # Minor component of the version of CVC4.
set(CVC4_RELEASE 0) # Release component of the version of CVC4.

# Extraversion component of the version of CVC4.
set(CVC4_EXTRAVERSION "-prerelease")

# Shared library versioning. Increment SOVERSION for every new CVC4 release.
set(CVC4_SOVERSION 6)

# Full release string for CVC4.
if(CVC4_RELEASE)
  set(CVC4_RELEASE_STRING
      "${CVC4_MAJOR}.${CVC4_MINOR}.${CVC4_RELEASE}${CVC4_EXTRAVERSION}")
else()
  set(CVC4_RELEASE_STRING "${CVC4_MAJOR}.${CVC4_MINOR}${CVC4_EXTRAVERSION}")
endif()

set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)
set(CMAKE_C_STANDARD 99)
set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_EXTENSIONS OFF)

# Generate compile_commands.json, which can be used for various code completion
# plugins.
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

#-----------------------------------------------------------------------------#
# Policies

# Required for FindGLPK since it sets CMAKE_REQUIRED_LIBRARIES
if(POLICY CMP0075)
  cmake_policy(SET CMP0075 NEW)
endif()

#-----------------------------------------------------------------------------#
# Tell CMake where to find our dependencies

if(ABC_DIR)
  list(APPEND CMAKE_PREFIX_PATH "${ABC_DIR}")
endif()
if(ANTLR_DIR)
  list(APPEND CMAKE_PREFIX_PATH "${ANTLR_DIR}")
endif()
if(CADICAL_DIR)
  list(APPEND CMAKE_PREFIX_PATH "${CADICAL_DIR}")
endif()
if(CRYPTOMINISAT_DIR)
  list(APPEND CMAKE_PREFIX_PATH "${CRYPTOMINISAT_DIR}")
endif()
if(CXXTEST_DIR)
  list(APPEND CMAKE_PREFIX_PATH "${CXXTEST_DIR}")
endif()
if(DRAT2ER_DIR)
  list(APPEND CMAKE_PREFIX_PATH "${DRAT2ER_DIR}")
endif()
if(GLPK_DIR)
  list(APPEND CMAKE_PREFIX_PATH "${GLPK_DIR}")
endif()
if(GMP_DIR)
  list(APPEND CMAKE_PREFIX_PATH "${GMP_DIR}")
endif()
if(KISSAT_DIR)
  list(APPEND CMAKE_PREFIX_PATH "${KISSAT_DIR}")
endif()
if(LFSC_DIR)
  list(APPEND CMAKE_PREFIX_PATH "${LFSC_DIR}")
endif()
if(SYMFPU_DIR)
  list(APPEND CMAKE_PREFIX_PATH "${SYMFPU_DIR}")
endif()

# By default the contrib/get-* scripts install dependencies to deps/install.
list(APPEND CMAKE_PREFIX_PATH "${PROJECT_SOURCE_DIR}/deps/install")

#-----------------------------------------------------------------------------#

set(INCLUDE_INSTALL_DIR include)
set(LIBRARY_INSTALL_DIR lib)
set(RUNTIME_INSTALL_DIR bin)

#-----------------------------------------------------------------------------#

# Embed the installation prefix as an RPATH in the executable such that the
# linker can find our libraries (such as libcvc4parser) when executing the cvc4
# binary. This is for example useful when installing CVC4 with a custom prefix
# on macOS (e.g. when using homebrew in a non-standard directory). If we do not
# set this option, then the linker will not be able to find the required
# libraries when trying to run CVC4.
#
# More information on RPATH in CMake:
# https://gitlab.kitware.com/cmake/community/wikis/doc/cmake/RPATH-handling
set(CMAKE_INSTALL_RPATH "${CMAKE_INSTALL_PREFIX}/${LIBRARY_INSTALL_DIR}")

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
cvc4_option(ENABLE_ASAN           "Enable ASAN build")
cvc4_option(ENABLE_UBSAN          "Enable UBSan build")
cvc4_option(ENABLE_TSAN           "Enable TSan build")
cvc4_option(ENABLE_ASSERTIONS     "Enable assertions")
cvc4_option(ENABLE_COMP_INC_TRACK
            "Enable optimizations for incremental SMT-COMP tracks")
cvc4_option(ENABLE_DEBUG_SYMBOLS  "Enable debug symbols")
cvc4_option(ENABLE_DUMPING        "Enable dumping")
cvc4_option(ENABLE_MUZZLE         "Suppress ALL non-result output")
cvc4_option(ENABLE_PROOFS         "Enable proof support")
cvc4_option(ENABLE_STATISTICS     "Enable statistics")
cvc4_option(ENABLE_TRACING        "Enable tracing")
cvc4_option(ENABLE_UNIT_TESTING   "Enable unit testing")
cvc4_option(ENABLE_VALGRIND       "Enable valgrind instrumentation")
cvc4_option(ENABLE_SHARED         "Build as shared library")
cvc4_option(ENABLE_STATIC_BINARY
            "Build static binaries with statically linked system libraries")
# >> 2-valued: ON OFF
#    > for options where we don't need to detect if set by user (default: OFF)
option(ENABLE_BEST             "Enable dependencies known to give best performance")
option(ENABLE_COVERAGE         "Enable support for gcov coverage testing")
option(ENABLE_DEBUG_CONTEXT_MM "Enable the debug context memory manager")
option(ENABLE_PROFILING        "Enable support for gprof profiling")

# Optional dependencies
#
# >> 3-valued: IGNORE ON OFF
#    > allows to detect if set by user (default: IGNORE)
#    > only necessary for options set for ENABLE_BEST
cvc4_option(USE_ABC           "Use ABC for AIG bit-blasting")
cvc4_option(USE_CADICAL       "Use CaDiCaL SAT solver")
cvc4_option(USE_CLN           "Use CLN instead of GMP")
cvc4_option(USE_CRYPTOMINISAT "Use CryptoMiniSat SAT solver")
cvc4_option(USE_GLPK          "Use GLPK simplex solver")
cvc4_option(USE_KISSAT        "Use Kissat SAT solver")
cvc4_option(USE_READLINE      "Use readline for better interactive support")
# >> 2-valued: ON OFF
#    > for options where we don't need to detect if set by user (default: OFF)
option(USE_DRAT2ER            "Include drat2er for making eager BV proofs")
option(USE_LFSC               "Use LFSC proof checker")
option(USE_SYMFPU             "Use SymFPU for floating point support")
option(USE_PYTHON2            "Prefer using Python 2 (for Python bindings)")
option(USE_PYTHON3            "Prefer using Python 3 (for Python bindings)")

# Custom install directories for dependencies
# If no directory is provided by the user, we first check if the dependency was
# installed via the corresponding contrib/get-* script and if not found, we
# check the intalled system version. If the user provides a directory we
# immediately fail if the dependency was not found at the specified location.
set(ABC_DIR           "" CACHE STRING "Set ABC install directory")
set(ANTLR_DIR         "" CACHE STRING "Set ANTLR3 install directory")
set(CADICAL_DIR       "" CACHE STRING "Set CaDiCaL install directory")
set(CRYPTOMINISAT_DIR "" CACHE STRING "Set CryptoMiniSat install directory")
set(CXXTEST_DIR       "" CACHE STRING "Set CxxTest install directory")
set(DRAT2ER_DIR       "" CACHE STRING "Set drat2er install directory")
set(GLPK_DIR          "" CACHE STRING "Set GLPK install directory")
set(GMP_DIR           "" CACHE STRING "Set GMP install directory")
set(KISSAT_DIR        "" CACHE STRING "Set Kissat install directory")
set(LFSC_DIR          "" CACHE STRING "Set LFSC install directory")
set(SYMFPU_DIR        "" CACHE STRING "Set SymFPU install directory")

# Prepend binaries with prefix on make install
set(PROGRAM_PREFIX    "" CACHE STRING "Program prefix on make install")

# Supported SWIG language bindings
option(BUILD_SWIG_BINDINGS_JAVA   "Build Java bindings with SWIG")
option(BUILD_SWIG_BINDINGS_PYTHON "Build Python bindings with SWIG")

# Supprted language bindings based on new C++ API
option(BUILD_BINDINGS_PYTHON "Build Python bindings based on new C++ API ")

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
add_check_c_flag("-fexceptions")
add_check_c_cxx_flag("-Wno-deprecated")
add_check_cxx_flag("-Wsuggest-override")
add_check_cxx_flag("-Wnon-virtual-dtor")
add_check_c_cxx_flag("-Wimplicit-fallthrough")
add_check_c_cxx_flag("-Wshadow")

# Temporarily disable -Wclass-memaccess to suppress 'no trivial copy-assignment'
# cdlist.h warnings. Remove when fixed.
add_check_cxx_flag("-Wno-class-memaccess")

if (WIN32)
  set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl,--stack,100000000")
endif ()

#-----------------------------------------------------------------------------#
# Use ld.gold if available

execute_process(COMMAND ${CMAKE_C_COMPILER}
                -fuse-ld=gold
                -Wl,--version ERROR_QUIET OUTPUT_VARIABLE LD_VERSION)
if ("${LD_VERSION}" MATCHES "GNU gold")
  string(APPEND CMAKE_EXE_LINKER_FLAGS " -fuse-ld=gold")
  string(APPEND CMAKE_SHARED_LINKER_FLAGS " -fuse-ld=gold")
  string(APPEND CMAKE_MODULE_LINKER_FLAGS " -fuse-ld=gold")
  message(STATUS "Using GNU gold linker.")
endif ()

#-----------------------------------------------------------------------------#
# Option defaults (three-valued options (cvc4_option(...)))
#
# These options are only set if their value is IGNORE. Otherwise, the user
# already set the option, which we don't want to overwrite.

if(ENABLE_STATIC_BINARY)
  cvc4_set_option(ENABLE_SHARED OFF)
else()
  cvc4_set_option(ENABLE_SHARED ON)
endif()

#-----------------------------------------------------------------------------#
# Set options for best configuration

if(ENABLE_BEST)
  cvc4_set_option(USE_ABC ON)
  cvc4_set_option(USE_CADICAL ON)
  cvc4_set_option(USE_CLN ON)
  cvc4_set_option(USE_CRYPTOMINISAT ON)
  cvc4_set_option(USE_GLPK ON)
  cvc4_set_option(USE_READLINE ON)
endif()

# Only enable unit testing if assertions are enabled. Otherwise, unit tests
# that expect AssertionException to be thrown will fail.
if(NOT ENABLE_ASSERTIONS)
  set(ENABLE_UNIT_TESTING OFF)
endif()

#-----------------------------------------------------------------------------#
# Shared/static libraries
#
# This needs to be set before any find_package(...) command since we want to
# search for static libraries with suffix .a.

if(ENABLE_SHARED)
  set(BUILD_SHARED_LIBS ON)
  if(ENABLE_STATIC_BINARY)
    set(ENABLE_STATIC_BINARY OFF)
    message(WARNING "Disabling static binary since shared build is enabled.")
  endif()
else()
  set(CMAKE_FIND_LIBRARY_SUFFIXES .a ${CMAKE_FIND_LIBRARY_SUFFIXES})
  set(BUILD_SHARED_LIBS OFF)
  cvc4_set_option(ENABLE_STATIC_BINARY ON)

  # Never build unit tests as static binaries, otherwise we'll end up with
  # ~300MB per unit test.
  if(ENABLE_UNIT_TESTING)
    message(WARNING "Disabling unit tests since static build is enabled.")
    set(ENABLE_UNIT_TESTING OFF)
  endif()
endif()

#-----------------------------------------------------------------------------#
# Enable the ctest testing framework

# This needs to be enabled here rather than in subdirectory test in order to
# allow calling ctest from the root build directory.
enable_testing()

#-----------------------------------------------------------------------------#
# Check GCC version.
#
# GCC version 4.5.1 builds MiniSat incorrectly with -O2, which results in
# incorrect answers.

if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
  execute_process(
    COMMAND ${CMAKE_CXX_COMPILER} -dumpversion
    OUTPUT_VARIABLE GCC_VERSION
    OUTPUT_STRIP_TRAILING_WHITESPACE)
  if(GCC_VERSION VERSION_EQUAL "4.5.1")
    message(FATAL_ERROR
      "GCC 4.5.1's optimizer is known to build MiniSat incorrectly "
      "(and by extension CVC4).")
  endif()
endif()

#-----------------------------------------------------------------------------#
# Check options, find packages and configure build.

if(USE_PYTHON2)
  find_package(PythonInterp 2.7 REQUIRED)
elseif(USE_PYTHON3)
  find_package(PythonInterp 3 REQUIRED)
else()
  find_package(PythonInterp REQUIRED)
endif()

find_package(GMP REQUIRED)

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
  add_definitions(-DCVC4_USE_UBSAN)
endif()

if(ENABLE_TSAN)
  # -fsanitize=thread requires CMAKE_REQUIRED_FLAGS to be explicitely set,
  # otherwise the -fsanitize=thread check will fail while linking.
  set(CMAKE_REQUIRED_FLAGS -fsanitize=thread)
  add_required_c_cxx_flag("-fsanitize=thread")
  unset(CMAKE_REQUIRED_FLAGS)
endif()

if(ENABLE_ASSERTIONS)
  add_definitions(-DCVC4_ASSERTIONS)
else()
  add_definitions(-DNDEBUG)
endif()

if(ENABLE_COVERAGE)
  include(CodeCoverage)
  APPEND_COVERAGE_COMPILER_FLAGS()
  add_definitions(-DCVC4_COVERAGE)
  # Note: The ctest command returns a non-zero exit code if tests fail or run
  # into a timeout. As a consequence, the coverage report is not generated. To
  # prevent this we always return with exit code 0 after the ctest command has
  # finished.
  setup_target_for_coverage_gcovr_html(
    NAME coverage
    EXECUTABLE
      ctest -j${CTEST_NTHREADS} -LE "example"
        --output-on-failure $$ARGS || exit 0
    DEPENDS
      build-tests)
endif()

if(ENABLE_DEBUG_CONTEXT_MM)
  add_definitions(-DCVC4_DEBUG_CONTEXT_MEMORY_MANAGER)
endif()

if(ENABLE_DEBUG_SYMBOLS)
  add_check_c_cxx_flag("-ggdb3")
endif()

if(ENABLE_COMP_INC_TRACK)
  add_definitions(-DCVC4_SMTCOMP_APPLICATION_TRACK)
endif()

if(ENABLE_MUZZLE)
  add_definitions(-DCVC4_MUZZLE)
endif()

if(ENABLE_DUMPING)
  add_definitions(-DCVC4_DUMPING)
endif()

if(ENABLE_PROFILING)
  add_definitions(-DCVC4_PROFILING)
  add_check_c_cxx_flag("-pg")
endif()

if(ENABLE_PROOFS)
  set(RUN_REGRESSION_ARGS ${RUN_REGRESSION_ARGS} --enable-proof)
  add_definitions(-DCVC4_PROOF)
endif()

if(ENABLE_TRACING)
  add_definitions(-DCVC4_TRACING)
endif()

if(ENABLE_STATISTICS)
  add_definitions(-DCVC4_STATISTICS_ON)
endif()

if(ENABLE_VALGRIND)
  find_package(Valgrind REQUIRED)
  add_definitions(-DCVC4_VALGRIND)
endif()

if(USE_ABC)
  find_package(ABC REQUIRED)
  add_definitions(-DCVC4_USE_ABC ${ABC_ARCH_FLAGS})
endif()

if(USE_CADICAL)
  find_package(CaDiCaL REQUIRED)
  add_definitions(-DCVC4_USE_CADICAL)
endif()

if(USE_CLN)
  set(GPL_LIBS "${GPL_LIBS} cln")
  find_package(CLN 1.2.2 REQUIRED)
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
  add_definitions(-DCVC4_USE_CRYPTOMINISAT)
endif()

if(USE_DRAT2ER)
  find_package(Drat2Er REQUIRED)
  add_definitions(-DCVC4_USE_DRAT2ER)
endif()

if(USE_GLPK)
  set(GPL_LIBS "${GPL_LIBS} glpk")
  find_package(GLPK REQUIRED)
  add_definitions(-DCVC4_USE_GLPK)
endif()

if(USE_KISSAT)
  find_package(Kissat REQUIRED)
  add_definitions(-DCVC4_USE_KISSAT)
endif()

if(USE_LFSC)
  set(RUN_REGRESSION_ARGS ${RUN_REGRESSION_ARGS} --with-lfsc)
  find_package(LFSC REQUIRED)
  add_definitions(-DCVC4_USE_LFSC)
endif()

if(USE_READLINE)
  set(GPL_LIBS "${GPL_LIBS} readline")
  find_package(Readline REQUIRED)
  set(HAVE_LIBREADLINE 1)
  if(Readline_COMPENTRY_FUNC_RETURNS_CHARPTR)
    set(READLINE_COMPENTRY_FUNC_RETURNS_CHARP 1)
  endif()
endif()

if(USE_SYMFPU)
  find_package(SymFPU REQUIRED)
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
# Generate CVC4's cvc4autoconfig.h header

include(ConfigureCVC4)
configure_file(cvc4autoconfig.h.in cvc4autoconfig.h)
include_directories(${CMAKE_CURRENT_BINARY_DIR})

#-----------------------------------------------------------------------------#
# Add subdirectories

# signatures needs to come before src since it adds source files to libcvc4.
if(ENABLE_PROOFS)
  add_subdirectory(proofs/signatures)
endif()

add_subdirectory(doc)
add_subdirectory(src)
add_subdirectory(test)

if(BUILD_SWIG_BINDINGS_JAVA OR BUILD_SWIG_BINDINGS_PYTHON)
  add_subdirectory(src/bindings)
endif()

if(BUILD_BINDINGS_PYTHON)
  add_subdirectory(src/api/python)
endif()

#-----------------------------------------------------------------------------#
# Package configuration
#
# Export CVC4 targets to support find_package(CVC4) in other cmake projects.

include(CMakePackageConfigHelpers)

install(EXPORT cvc4-targets
  FILE CVC4Targets.cmake
  NAMESPACE CVC4::
  DESTINATION ${LIBRARY_INSTALL_DIR}/cmake/CVC4)

configure_package_config_file(
  ${CMAKE_SOURCE_DIR}/cmake/CVC4Config.cmake.in
  ${CMAKE_BINARY_DIR}/cmake/CVC4Config.cmake
  INSTALL_DESTINATION ${LIBRARY_INSTALL_DIR}/cmake/CVC4
  PATH_VARS LIBRARY_INSTALL_DIR
)

write_basic_package_version_file(
  ${CMAKE_CURRENT_BINARY_DIR}/CVC4ConfigVersion.cmake
  VERSION ${CVC4_RELEASE_STRING}
  COMPATIBILITY ExactVersion
)

install(FILES
  ${CMAKE_BINARY_DIR}/cmake/CVC4Config.cmake
  ${CMAKE_BINARY_DIR}/CVC4ConfigVersion.cmake
  DESTINATION ${LIBRARY_INSTALL_DIR}/cmake/CVC4
)


#-----------------------------------------------------------------------------#
# Print build configuration

# Convert build type to lower case.
string(TOLOWER ${CMAKE_BUILD_TYPE} CVC4_BUILD_PROFILE_STRING)

# Get all definitions added via add_definitions.
get_directory_property(CVC4_DEFINITIONS COMPILE_DEFINITIONS)
string(REPLACE ";" " " CVC4_DEFINITIONS "${CVC4_DEFINITIONS}")

message("CVC4 ${CVC4_RELEASE_STRING}")
message("")
if(ENABLE_COMP_INC_TRACK)
  message("Build profile             : ${CVC4_BUILD_PROFILE_STRING} (incremental)")
else()
  message("Build profile             : ${CVC4_BUILD_PROFILE_STRING}")
endif()
message("")
print_config("GPL                       :" ENABLE_GPL)
print_config("Best configuration        :" ENABLE_BEST)
print_config("Optimization level        :" OPTIMIZATION_LEVEL)
message("")
print_config("Assertions                :" ENABLE_ASSERTIONS)
print_config("Debug symbols             :" ENABLE_DEBUG_SYMBOLS)
print_config("Debug context mem mgr     :" ENABLE_DEBUG_CONTEXT_MM)
message("")
print_config("Dumping                   :" ENABLE_DUMPING)
print_config("Muzzle                    :" ENABLE_MUZZLE)
print_config("Proofs                    :" ENABLE_PROOFS)
print_config("Statistics                :" ENABLE_STATISTICS)
print_config("Tracing                   :" ENABLE_TRACING)
message("")
print_config("ASan                      :" ENABLE_ASAN)
print_config("UBSan                     :" ENABLE_UBSAN)
print_config("TSan                      :" ENABLE_TSAN)
print_config("Coverage (gcov)           :" ENABLE_COVERAGE)
print_config("Profiling (gprof)         :" ENABLE_PROFILING)
print_config("Unit tests                :" ENABLE_UNIT_TESTING)
print_config("Valgrind                  :" ENABLE_VALGRIND)
message("")
print_config("Shared libs               :" ENABLE_SHARED)
print_config("Static binary             :" ENABLE_STATIC_BINARY)
print_config("Java SWIG bindings        :" BUILD_SWIG_BINDINGS_JAVA)
print_config("Python SWIG bindings      :" BUILD_SWIG_BINDINGS_PYTHON)
print_config("Python bindings           :" BUILD_BINDINGS_PYTHON)
print_config("Python2                   :" USE_PYTHON2)
print_config("Python3                   :" USE_PYTHON3)
message("")
print_config("ABC                       :" USE_ABC)
print_config("CaDiCaL                   :" USE_CADICAL)
print_config("CryptoMiniSat             :" USE_CRYPTOMINISAT)
print_config("drat2er                   :" USE_DRAT2ER)
print_config("GLPK                      :" USE_GLPK)
print_config("Kissat                    :" USE_KISSAT)
print_config("LFSC                      :" USE_LFSC)

if(CVC4_USE_CLN_IMP)
  message("MP library                : cln")
else()
  message("MP library                : gmp")
endif()
print_config("Readline                  :" ${USE_READLINE})
print_config("SymFPU                    :" ${USE_SYMFPU})
message("")
if(ABC_DIR)
  message("ABC dir                   : ${ABC_DIR}")
endif()
if(ANTLR_DIR)
  message("ANTLR dir                 : ${ANTLR_DIR}")
endif()
if(CADICAL_DIR)
  message("CADICAL dir               : ${CADICAL_DIR}")
endif()
if(CRYPTOMINISAT_DIR)
  message("CRYPTOMINISAT dir         : ${CRYPTOMINISAT_DIR}")
endif()
if(DRAT2ER_DIR)
  message("DRAT2ER dir               : ${DRAT2ER_DIR}")
endif()
if(GLPK_DIR)
  message("GLPK dir                  : ${GLPK_DIR}")
endif()
if(GMP_DIR)
  message("GMP dir                   : ${GMP_DIR}")
endif()
if(KISSAT_DIR)
  message("KISSAT dir                : ${KISSAT_DIR}")
endif()
if(LFSC_DIR)
  message("LFSC dir                  : ${LFSC_DIR}")
endif()
if(SYMFPU_DIR)
  message("SYMFPU dir                : ${SYMFPU_DIR}")
endif()
message("")
message("CPPLAGS (-D...)           : ${CVC4_DEFINITIONS}")
message("CXXFLAGS                  : ${CMAKE_CXX_FLAGS}")
message("CFLAGS                    : ${CMAKE_C_FLAGS}")
message("Linker flags              : ${CMAKE_EXE_LINKER_FLAGS}")
message("")
message("Install prefix            : ${CMAKE_INSTALL_PREFIX}")
message("")

if(GPL_LIBS)
  message(
  "CVC4 license             : GPLv3 (due to optional libraries; see below)"
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
  "disable all optional GPLed library dependencies (-DENABLE_BSD_ONLY=ON)."
  )
else()
  message(
  "CVC4 license              : modified BSD"
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
