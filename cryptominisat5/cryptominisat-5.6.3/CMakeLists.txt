# Copyright (c) 2017, Mate Soos
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

cmake_minimum_required(VERSION 3.3 FATAL_ERROR)
set(CMAKE_C_STANDARD 99)
set(CMAKE_CXX_STANDARD 11)

include (GenerateExportHeader)
include (GNUInstallDirs)

message(STATUS "LIB directory is '${CMAKE_INSTALL_LIBDIR}'")
message(STATUS "BIN directory is '${CMAKE_INSTALL_BINDIR}'")

if(POLICY CMP0048)
    #policy for VERSION in cmake 3.0
    cmake_policy(SET CMP0048 NEW)
endif()


if(POLICY CMP0022)
    cmake_policy(SET CMP0022 NEW)
endif()

if(POLICY CMP0046)
    cmake_policy(SET CMP0046 NEW)
endif()

if(POLICY CMP0026)
    cmake_policy(SET CMP0026 NEW)
endif()

# -----------------------------------------------------------------------------
# Provide scripts dir for included cmakes to use
# -----------------------------------------------------------------------------
set(CRYPTOMS_SCRIPTS_DIR ${CMAKE_CURRENT_SOURCE_DIR}/scripts)

# -----------------------------------------------------------------------------
# Make RelWithDebInfo the default build type if otherwise not set
# -----------------------------------------------------------------------------
set(build_types Debug Release RelWithDebInfo MinSizeRel)
if(NOT CMAKE_BUILD_TYPE)
    message(STATUS "You can choose the type of build, options are:${build_types}")
    set(CMAKE_BUILD_TYPE RelWithDebInfo CACHE String
        "Options are ${build_types}"
        FORCE
    )

    # Provide drop down menu options in cmake-gui
    set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS ${build_types})
endif()
message(STATUS "Doing a ${CMAKE_BUILD_TYPE} build")

# -----------------------------------------------------------------------------
# Option to enable/disable assertions
# -----------------------------------------------------------------------------

# Filter out definition of NDEBUG from the default build configuration flags.
# We will add this ourselves if we want to disable assertions
foreach (build_config ${build_types})
    string(TOUPPER ${build_config} upper_case_build_config)
    foreach (language CXX C)
        set(VAR_TO_MODIFY "CMAKE_${language}_FLAGS_${upper_case_build_config}")
        string(REGEX REPLACE "(^| )[/-]D *NDEBUG($| )"
                             " "
                             replacement
                             "${${VAR_TO_MODIFY}}")
        #message("Original (${VAR_TO_MODIFY}) is ${${VAR_TO_MODIFY}} replacement is ${replacement}")
        set(${VAR_TO_MODIFY} "${replacement}" CACHE STRING "Default flags for ${build_config} configuration" FORCE)
    endforeach()
endforeach()

PROJECT(cryptominisat5)

# contains some library search cmake scripts
SET(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)

# generate JSON file of compile commands -- useful for code extension
set(CMAKE_EXPORT_COMPILE_COMMANDS 1)

set(THREADS_PREFER_PTHREAD_FLAG ON)
find_package (Threads REQUIRED)

option(EMSCRIPTEN "Generate only emscripten JS" OFF)

option(FEEDBACKFUZZ "Use Clang coverage sanitizers" OFF)
if (FEEDBACKFUZZ)
    SET (CMAKE_CXX_COMPILER "clang++")
    add_compile_options("-fsanitize=address")
    add_compile_options("-fsanitize-coverage=edge,indirect-calls,8bit-counters")
endif()

option(LARGEMEM "Allow memory usage to grow to Terabyte values -- uses 64b offsets. Slower, but allows the solver to run for much longer." OFF)
if (LARGEMEM)
    add_definitions(-DLARGE_OFFSETS)
endif()

macro(add_sanitize_option flagname)
    SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flagname}" )
endmacro()

option(SANITIZE "Use Clang sanitizers. You MUST use clang++ as the compiler for this to work" OFF)

include(CheckCXXCompilerFlag)
macro(add_cxx_flag_if_supported flagname)
  check_cxx_compiler_flag("${flagname}" HAVE_FLAG_${flagname})

  if(HAVE_FLAG_${flagname})
    SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flagname}" )
  endif()
endmacro()

macro(add_sanitize_flags)
if (SANITIZE)
    MESSAGE(WARNING "Using clang sanitizers -- you MUST use clang++ or the compile WILL fail")
    add_sanitize_option("-fsanitize=address")
    add_sanitize_option("-fsanitize=integer")
    add_sanitize_option("-fsanitize=undefined")

    add_sanitize_option("-fsanitize=null")
    add_sanitize_option("-fsanitize=alignment")
    #add_sanitize_option("-fno-sanitize-recover")

    add_sanitize_option("-fsanitize=return")
    add_sanitize_option("-fsanitize=bounds")
    add_sanitize_option("-fsanitize=float-divide-by-zero")
    add_sanitize_option("-fsanitize=integer-divide-by-zero")
    add_sanitize_option("-fsanitize=unsigned-integer-overflow")
    add_sanitize_option("-fsanitize=signed-integer-overflow")
    add_sanitize_option("-fsanitize=bool")
    add_sanitize_option("-fsanitize=enum")
    add_sanitize_option("-fsanitize=float-cast-overflow")

    #add_sanitize_option("-Weverything")
    #add_sanitize_option("-Wshorten-64-to-32")
    #add_sanitize_option("-Wweak-vtables")
    #add_sanitize_option("-Wsign-conversion")
    #add_sanitize_option("-Wconversion")
endif()
endmacro()

option(USE_GAUSS "Build with every-level GAUSS enabled" OFF)
if (USE_GAUSS)
    add_definitions(-DUSE_GAUSS)
    message(STATUS "Building with GAUSS enabled at every level")
endif()

option(ENABLE_ASSERTIONS "Build with assertions enabled" ON)
message(STATUS "build type is ${CMAKE_BUILD_TYPE}")
if(CMAKE_BUILD_TYPE STREQUAL "Release")
    set(ENABLE_ASSERTIONS OFF)
endif()

if (ENABLE_ASSERTIONS)
    # NDEBUG was already removed.
else()
    # Note this definition doesn't appear in the cache variables.
    add_definitions(-DNDEBUG)
    add_cxx_flag_if_supported("-fno-stack-protector")
    add_definitions(-D_FORTIFY_SOURCE=0)
endif()

# Note: O3 gives slight speed increase, 1 more solved from SAT Comp'14 @ 3600s
if (NOT MSVC)
    add_compile_options( -g)
    add_compile_options( -pthread )

    add_compile_options("$<$<CONFIG:RELWITHDEBINFO>:-O2>")
    add_compile_options("$<$<CONFIG:RELWITHDEBINFO>:-mtune=native>")

    add_compile_options("$<$<CONFIG:RELEASE>:-O2>")
    add_compile_options("$<$<CONFIG:RELEASE>:-g0>")
    add_compile_options("$<$<CONFIG:RELEASE>:-mtune=native>")

    add_compile_options("$<$<CONFIG:DEBUG>:-O0>")

    if(NOT CMAKE_BUILD_TYPE STREQUAL "Debug")
        set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -O2")
        set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -O2")
    endif()

else()
    # see https://msdn.microsoft.com/en-us/library/fwkeyyhe.aspx for details
    # /ZI = include debug info
    # /Wall = all warnings

    add_compile_options("$<$<CONFIG:RELWITHDEBINFO>:/Ox>")
    add_compile_options("$<$<CONFIG:RELWITHDEBINFO>:/ZI>")

    add_compile_options("$<$<CONFIG:RELEASE>:/Ox>")
    add_compile_options("$<$<CONFIG:RELEASE>:/D>")
    add_compile_options("$<$<CONFIG:RELEASE>:/NDEBUG>")
    add_compile_options("$<$<CONFIG:RELEASE>:/ZI>")

    add_compile_options("$<$<CONFIG:DEBUG>:/Od>")

    if (STATICCOMPILE)
        # We statically link to reduce dependencies
        foreach(flag_var CMAKE_CXX_FLAGS CMAKE_CXX_FLAGS_DEBUG CMAKE_CXX_FLAGS_RELEASE CMAKE_CXX_FLAGS_MINSIZEREL CMAKE_CXX_FLAGS_RELWITHDEBINFO)
            # /MD -- Causes the application to use the multithread-specific and DLL-specific version of the run-time library.
            #        Defines _MT and _DLL and causes the compiler to place the library name MSVCRT.lib into the .obj file.
            if(${flag_var} MATCHES "/MD")
                string(REGEX REPLACE "/MD" "/MT" ${flag_var} "${${flag_var}}")
            endif(${flag_var} MATCHES "/MD")

            # /MDd	-- Defines _DEBUG, _MT, and _DLL and causes the application to use the debug multithread-specific and DLL-specific version of the run-time library.
            #          It also causes the compiler to place the library name MSVCRTD.lib into the .obj file.
            if(${flag_var} MATCHES "/MDd")
                string(REGEX REPLACE "/MDd" "/MTd" ${flag_var} "${${flag_var}}")
            endif(${flag_var} MATCHES "/MDd")
        endforeach(flag_var)

        # Creates a multithreaded executable (static) file using LIBCMT.lib.
        add_compile_options(/MT)
    endif()

    # buffers security check
    add_compile_options(/GS)

    # Proper warning level
    add_compile_options(/W1)

    # Disable STL used in DLL-boundary warning
    add_compile_options(/wd4251)
    add_compile_options(/D_CRT_SECURE_NO_WARNINGS)

    # Wall is MSVC's Weverything, so annoying unless used from the start
    # and with judiciously used warning disables
    # add_compile_options(/Wall)

    # /Za = only ansi C98 & C++11
    # /Za is not recommended for use, not tested, etc.
    # see: http://stackoverflow.com/questions/5489326/za-compiler-directive-does-not-compile-system-headers-in-vs2010
    # add_compile_options(/Za)

    add_compile_options(/fp:precise)

    # exception handling. s = The exception-handling model that catches C++ exceptions only and tells the compiler to assume that functions declared as extern "C" may throw an exception.
    # exception handling. c = If used with s (/EHsc), catches C++ exceptions only and tells the compiler to assume that functions declared as extern "C" never throw a C++ exception.
    add_compile_options(/EHsc)


    set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} /INCREMENTAL:NO")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} /PDBCOMPRESS")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} /STACK:1572864")

    #what does this do?
    set(DEF_INSTALL_CMAKE_DIR CMake)
endif()

option(ENABLE_TESTING "Enable testing" OFF)
option(COVERAGE "Build with coverage check" OFF)
option(STATICCOMPILE "Compile to static executable" OFF)
if (COVERAGE AND NOT STATICCOMPILE)
    MESSAGE(FATAL_ERROR "Coverage can only be computed on static compilation")
endif()

if (NOT WIN32)
    if(NOT ENABLE_TESTING AND ${CMAKE_SYSTEM_NAME} MATCHES "Linux" AND NOT COVERAGE)
        #dd_cxx_flag_if_supported("-fvisibility=hidden")
    endif()
    add_compile_options("-fPIC")

    if(CMAKE_BUILD_TYPE STREQUAL "Release")
        #add_cxx_flag_if_supported("-flto")
    else()
        add_cxx_flag_if_supported("-mtune=native")
        add_cxx_flag_if_supported("-Wall")
        add_cxx_flag_if_supported("-Wextra")
        add_cxx_flag_if_supported("-Wunused")
        add_cxx_flag_if_supported("-Wsign-compare")
        if (NOT CMAKE_BUILD_TYPE STREQUAL "Release")
            add_cxx_flag_if_supported("-fno-omit-frame-pointer")
        endif()
        add_cxx_flag_if_supported("-Wtype-limits")
        add_cxx_flag_if_supported("-Wuninitialized")
        add_cxx_flag_if_supported("-Wno-deprecated")
        add_cxx_flag_if_supported("-Wstrict-aliasing")
        add_cxx_flag_if_supported("-Wpointer-arith")
        add_cxx_flag_if_supported("-Wheader-guard")
        add_cxx_flag_if_supported("-Wpointer-arith")
        add_cxx_flag_if_supported("-Wformat-nonliteral")
        add_cxx_flag_if_supported("-Winit-self")
        add_cxx_flag_if_supported("-Wparentheses")
        add_cxx_flag_if_supported("-Wunreachable-code")
        add_cxx_flag_if_supported("-ggdb3")
    endif()
endif()

if (COVERAGE)
    add_compile_options("--coverage")
    SET(CMAKE_EXE_LINKER_FLAGS "--coverage")
endif()


option(IPASIR "Also build IPASIR" OFF)

option(LIMITMEM "*Only used for testing*. Limit memory used by CMS through number of variables" OFF)
if (LIMITMEM)
    add_definitions(-DLIMITMEM)
endif()

# -----------------------------------------------------------------------------
# Uncomment these for static compilation under Linux (messes up Valgrind)
# -----------------------------------------------------------------------------
if (${CMAKE_SYSTEM_NAME} MATCHES "Linux" AND NOT SANITIZE)
    set(CMAKE_EXE_LINKER_FLAGS " ${CMAKE_EXE_LINKER_FLAGS} -Wl,--discard-all -Wl,--build-id=sha1")
endif()

if ((${CMAKE_SYSTEM_NAME} MATCHES "Linux") OR (${CMAKE_SYSTEM_NAME} MATCHES "Darwin"))
    if(STATICCOMPILE)
        MESSAGE(STATUS "Compiling for static library use")
        if (${CMAKE_SYSTEM_NAME} MATCHES "Linux")
            set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static -Wl,--whole-archive -ldl -lpthread -Wl,--no-whole-archive -static ")
        endif()

        SET(CMAKE_FIND_LIBRARY_SUFFIXES ".a")

        # removing -rdynamic that's automatically added
        foreach (language CXX C)
            set(VAR_TO_MODIFY "CMAKE_SHARED_LIBRARY_LINK_${language}_FLAGS")
            string(REGEX REPLACE "(^| )-rdynamic($| )"
                                 " "
                                 replacement
                                 "${${VAR_TO_MODIFY}}")
            #message("Original (${VAR_TO_MODIFY}) is ${${VAR_TO_MODIFY}} replacement is ${replacement}")
            set(${VAR_TO_MODIFY} "${replacement}" CACHE STRING "Default flags for ${build_config} configuration" FORCE)
        endforeach()
    else()
        add_definitions(-DBOOST_TEST_DYN_LINK)
        MESSAGE(STATUS "Compiling for dynamic library use")
    endif()
endif()

if ((${CMAKE_SYSTEM_NAME} MATCHES "Windows") AND (STATICCOMPILE))
    set(Boost_USE_STATIC_LIBS ON)
endif()

if(NOT MSVC)
  set(DEF_INSTALL_CMAKE_DIR lib/cmake/cryptominisat5)
endif()

option(SLOW_DEBUG "Use more debug flags" OFF)
IF(SLOW_DEBUG)
    add_definitions(-DSLOW_DEBUG)
endif()

# -----------------------------------------------------------------------------
# Add GIT version
# -----------------------------------------------------------------------------
function(SetVersionNumber PREFIX VERSION_MAJOR VERSION_MINOR VERSION_PATCH)
  set(${PREFIX}_VERSION_MAJOR ${VERSION_MAJOR} PARENT_SCOPE)
  set(${PREFIX}_VERSION_MINOR ${VERSION_MINOR} PARENT_SCOPE)
  set(${PREFIX}_VERSION_PATCH ${VERSION_PATCH} PARENT_SCOPE)
  set(${PREFIX}_VERSION
        "${VERSION_MAJOR}.${VERSION_MINOR}.${VERSION_PATCH}"
        PARENT_SCOPE)
endfunction()

find_program (GIT_EXECUTABLE git)
if (GIT_EXECUTABLE)
  include(GetGitRevisionDescription)
  get_git_head_revision(GIT_REFSPEC GIT_SHA1)
  MESSAGE(STATUS "GIT hash found: ${GIT_SHA1}")
else()
  set(GIT_SHA "GIT-hash-notfound")
endif()
set(CMS_FULL_VERSION "5.6.3")

string(REPLACE "." ";" CMS_FULL_VERSION_LIST ${CMS_FULL_VERSION})
SetVersionNumber("PROJECT" ${CMS_FULL_VERSION_LIST})
MESSAGE(STATUS "PROJECT_VERSION: ${PROJECT_VERSION}")
MESSAGE(STATUS "PROJECT_VERSION_MAJOR: ${PROJECT_VERSION_MAJOR}")
MESSAGE(STATUS "PROJECT_VERSION_MINOR: ${PROJECT_VERSION_MINOR}")
MESSAGE(STATUS "PROJECT_VERSION_PATCH: ${PROJECT_VERSION_PATCH}")

option(ONLY_SIMPLE "Only build very simplistic executable -- no Boost needed" OFF)

if (NOT ONLY_SIMPLE)
    set (boost_components "")
    set(boost_components ${boost_components} program_options)
    find_package( Boost 1.46 COMPONENTS ${boost_components})
endif()

option(STATS "Don't use statistics at all" OFF)
if (STATS)
    add_definitions( -DSTATS_NEEDED )
    if (NOT NOSQLITE)
        find_package(Sqlite3)
        IF (SQLITE3_FOUND)
            MESSAGE(STATUS "OK, Found Sqlite3!")
            include_directories(${SQLITE3_INCLUDE_DIR})
            add_definitions( -DUSE_SQLITE3 )
            set(USING_SQLITE ON)
        else ()
            MESSAGE(STATUS "WARNING: Did not find Sqlite3, Sqlite3 support will be disabled")
        endif ()
    endif()
ELSE ()
    MESSAGE(STATUS "Not compiling detailed statistics. The system is faster without them")
ENDIF ()

# ----------
# manpage
# ----------
if (${CMAKE_SYSTEM_NAME} MATCHES "Linux")
    find_program(HELP2MAN_FOUND help2man)
    if (HELP2MAN_FOUND)

        set(mandir ${CMAKE_INSTALL_PREFIX}/share/man/man1)
        # INSTALL(CODE "FILE(MAKE_DIRECTORY ${mandir})")


        if (NOT ONLY_SIMPLE)
            ADD_CUSTOM_TARGET(man_cms5
                ALL
                DEPENDS cryptominisat5
            )

            ADD_CUSTOM_COMMAND(
                TARGET man_cms5
                COMMAND help2man
                ARGS --version-string=${CMS_FULL_VERSION} --help-option="--hhelp" $<TARGET_FILE:cryptominisat5> -o ${CMAKE_CURRENT_BINARY_DIR}/cryptominisat5.1
            )

            INSTALL(
                FILES ${CMAKE_CURRENT_BINARY_DIR}/cryptominisat5.1
                DESTINATION ${mandir}
            )

        endif()
        ADD_CUSTOM_TARGET(man_cms5_simple
            ALL
            DEPENDS cryptominisat5_simple
        )

        ADD_CUSTOM_COMMAND(
            TARGET man_cms5_simple
            COMMAND help2man
            ARGS --version-string=${CMS_FULL_VERSION} --help-option="-h" $<TARGET_FILE:cryptominisat5_simple> -o ${CMAKE_CURRENT_BINARY_DIR}/cryptominisat5_simple.1
        )

        INSTALL(
            FILES ${CMAKE_CURRENT_BINARY_DIR}/cryptominisat5_simple.1
            DESTINATION ${mandir}
        )

        message(STATUS "Manpage will be created and installed")
    else()
        MESSAGE(STATUS "Cannot find help2man, not creating manpage")
    endif()
else()
    MESSAGE(STATUS "Not on Linux, not creating manpage")
endif()

# -----------------------------------------------------------------------------
# Look for ZLIB (For reading zipped CNFs)
# -----------------------------------------------------------------------------
option(NOZLIB "Don't use zlib" OFF)

# cannot currently compile static zlib under Windows
if (NOT NOZLIB AND NOT (STATICCOMPILE AND WIN32))
    find_package(ZLIB)
    IF (ZLIB_FOUND)
        MESSAGE(STATUS "OK, Found ZLIB!")
        include_directories(${ZLIB_INCLUDE_DIR})
        link_directories(${ZLIB_LIB_DIR})
        add_definitions( -DUSE_ZLIB )
    ELSE (ZLIB_FOUND)
        MESSAGE(STATUS "WARNING: Did not find ZLIB, gzipped file support will be disabled")
    ENDIF (ZLIB_FOUND)
endif()

option(NOVALGRIND "Don't use valgrind" ON)
find_package(Valgrind)
if (VALGRIND_FOUND AND NOT NOVALGRIND)
    message(STATUS "OK, Found Valgrind. Using valgrind client requests to mark freed clauses in pool as undefined")
    add_definitions(-DUSE_VALGRIND)
    include_directories(${VALGRIND_INCLUDE_DIR})
else()
    message(STATUS "Cannot find valgrind or it's disabled, we will not be able to mark memory pool objects as undefined")
endif()

# -----------------------------------------------------------------------------
# Look for M4RI (for Gauss)
# -----------------------------------------------------------------------------
option(REQUIRE_M4RI "Must use m4ri" OFF)
option(NOM4RI "Don't use m4ri" OFF)
if (NOT NOM4RI)
    find_package(M4RI)
    IF (M4RI_FOUND)
        MESSAGE(STATUS "OK, Found M4RI lib at ${M4RI_LIBRARIES} and includes at ${M4RI_INCLUDE_DIRS}")
        add_definitions( -DUSE_M4RI )
    ELSE (M4RI_FOUND)
        MESSAGE(WARNING "Did not find M4RI, XOR detection&manipulation disabled")
        if (REQUIRE_M4RI)
            MESSAGE(FATAL_ERROR "REQUIRE_M4RI was set but M4RI was not found!")
        endif()
    ENDIF (M4RI_FOUND)
endif()

#query definitions
get_directory_property( DirDefs DIRECTORY ${CMAKE_SOURCE_DIR} COMPILE_DEFINITIONS )
set(COMPILE_DEFINES)
foreach( d ${DirDefs} )
    # message( STATUS "Found Define: " ${d} )
    set(COMPILE_DEFINES "${COMPILE_DEFINES} -D${d}")
endforeach()
message(STATUS "All defines at startup: ${COMPILE_DEFINES}")


set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/lib)
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/lib)

macro(cmsat_add_public_header LIBTARGET HEADER)
    get_target_property(EXISTING_PUBLIC_HEADERS ${LIBTARGET} PUBLIC_HEADER)
    if(EXISTING_PUBLIC_HEADERS)
        list(APPEND EXISTING_PUBLIC_HEADERS "${HEADER}")
    else()
        # Do not append to empty list
        set(EXISTING_PUBLIC_HEADERS "${HEADER}")
    endif()
    set_target_properties(
        ${LIBTARGET}
        PROPERTIES
        PUBLIC_HEADER "${EXISTING_PUBLIC_HEADERS}"
     )
endmacro()

# -----------------------------------------------------------------------------
# Look for python
# -----------------------------------------------------------------------------
option(ENABLE_PYTHON_INTERFACE "Enable Python interface" ON)
option(FORCE_PYTHON2 OFF)
if (NOT FORCE_PYTHON2)
    find_package(PythonInterp 3)
    find_package(PythonLibs 3)
    message(STATUS "Python 3 -- PYTHON_EXECUTABLE=${PYTHON_EXECUTABLE}")
    message(STATUS "Python 3 -- PYTHON_LIBRARIES=${PYTHON_LIBRARIES}")
    message(STATUS "Python 3 -- PYTHON_INCLUDE_DIRS=${PYTHON_INCLUDE_DIRS}")
    message(STATUS "Python 3 -- PYTHONLIBS_VERSION_STRING=${PYTHONLIBS_VERSION_STRING}")
endif()

if (NOT (PYTHONINTERP_FOUND AND PYTHONLIBS_FOUND AND PYTHON_INCLUDE_DIRS))
    unset(PYTHONLIBS_FOUND CACHE)
    unset(PYTHON_LIBRARIES CACHE)
    unset(PYTHON_INCLUDE_PATH CACHE)
    unset(PYTHON_INCLUDE_DIRS CACHE)
    unset(PYTHON_DEBUG_LIBRARIES CACHE)
    unset(PYTHONLIBS_VERSION_STRING CACHE)

    unset(PYTHONINTERP_FOUND CACHE)
    unset(PYTHON_EXECUTABLE CACHE)
    unset(PYTHON_VERSION_STRING CACHE)

    message(STATUS "Python 3 not fully found or Python 2 has been forced -- trying Python 2.7")
    find_package(PythonInterp 2.7)
    find_package(PythonLibs 2.7)

    message(STATUS "Python 2.7 -- PYTHON_EXECUTABLE=${PYTHON_EXECUTABLE}")
    message(STATUS "Python 2.7 -- PYTHON_LIBRARIES=${PYTHON_LIBRARIES}")
    message(STATUS "Python 2.7 -- PYTHON_INCLUDE_DIRS=${PYTHON_INCLUDE_DIRS}")
    message(STATUS "Python 2.7 -- PYTHONLIBS_VERSION_STRING=${PYTHONLIBS_VERSION_STRING}")
endif()

#command-line parsing executable needs boost program-options
if(NOT Boost_FOUND)
    set(ONLY_SIMPLE ON)
    message(STATUS "Only building executable with few command-line options because the boost program_options library were not available")
endif()

# -----------------------------------------------------------------------------
# Provide an export name to be used by targets that wish to export themselves.
# -----------------------------------------------------------------------------
set(CRYPTOMINISAT5_EXPORT_NAME "cryptominisat5Targets")

add_subdirectory(src cmsat5-src)

# -----------------------------------------------------------------------------
# Add uninstall target for makefiles
# -----------------------------------------------------------------------------
configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/cmake/cmake_uninstall.cmake.in"
    "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake"
    IMMEDIATE @ONLY
)

add_custom_target(uninstall
    COMMAND ${CMAKE_COMMAND} -P ${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake
    DEPENDS uninstall_pycyrptosat
)

# -----------------------------------------------------------------------------
# Testing
# -----------------------------------------------------------------------------
if (ENABLE_TESTING)
    enable_testing()

    #use valgrind
    find_program(MEMORYCHECK_COMMAND valgrind)
    if(MEMORYCHECK_COMMAND-NOTFOUND)
      message(WARNING "Valgrind not found. Test will be run without valgrind.")
    else()
      message(STATUS "Valgrind found: ${MEMORYCHECK_COMMAND}. Running test using it.")
      set(MEMORYCHECK_COMMAND_OPTIONS "--trace-children=yes --leak-check=full")
    endif()

    # too unstable to add (depends on CPU)
    #if (NOT STATS AND NOT SLOW_DEBUG)
        #add_test (NAME library_speed_test COMMAND tests/library_speed_test)
    #endif()

    message(STATUS "Testing is enabled")
    set(UNIT_TEST_EXE_SUFFIX "Tests" CACHE STRING "Suffix for Unit test executable")
    add_subdirectory(tests)
    add_subdirectory(scripts/fuzz)

else()
    message(WARNING "Testing is disabled")
endif()

if (ENABLE_PYTHON_INTERFACE)
    if (PYTHONINTERP_FOUND AND PYTHONLIBS_FOUND AND PYTHON_INCLUDE_DIRS AND NOT COVERAGE)
        message(STATUS "Found python interpreter, libs and header files")
        message(STATUS "Building python interface")
        add_subdirectory(python pycryptosat)
    else()
        message(WARNING "Cannot find python interpreter, libs and header files, cannot build python interface")
    endif()
endif()

# -----------------------------------------------------------------------------
# Export our targets so that other CMake based projects can interface with
# the build of cryptominisat5 in the build-tree
# -----------------------------------------------------------------------------
set(CRYPTOMINISAT5_TARGETS_FILENAME "cryptominisat5Targets.cmake")
set(CRYPTOMINISAT5_CONFIG_FILENAME "cryptominisat5Config.cmake")
set(CRYPTOMINISAT5_STATIC_DEPS
    ${SQLITE3_LIBRARIES}
    ${M4RI_LIBRARIES}
)

# Export targets
set(MY_TARGETS libcryptominisat5 cryptominisat5_simple)
if (NOT ONLY_SIMPLE)
    set(MY_TARGETS ${MY_TARGETS} cryptominisat5)
endif()
if (IPASIR)
    set(MY_TARGETS ${MY_TARGETS} ipasircryptominisat5)
endif()
export(
    TARGETS ${MY_TARGETS}
    FILE "${CMAKE_CURRENT_BINARY_DIR}/${CRYPTOMINISAT5_TARGETS_FILENAME}"
)

# Create cryptominisat5Config file
set(EXPORT_TYPE "Build-tree")
set(CONF_INCLUDE_DIRS "${CMAKE_CURRENT_BINARY_DIR}/include")
configure_file(cryptominisat5Config.cmake.in
    "${CMAKE_CURRENT_BINARY_DIR}/${CRYPTOMINISAT5_CONFIG_FILENAME}" @ONLY
)

set(CRYPTOMINISAT5_INSTALL_CMAKE_DIR ${DEF_INSTALL_CMAKE_DIR} CACHE PATH
    "Installation directory for cryptominisat5 CMake files")

# Create cryptominisat5Config file
set(EXPORT_TYPE "installed")
set(CONF_INCLUDE_DIRS "${CMAKE_INSTALL_PREFIX}/include")
configure_file(cryptominisat5Config.cmake.in
   "${CMAKE_CURRENT_BINARY_DIR}/${CMAKE_FILES_DIRECTORY}/${CRYPTOMINISAT5_CONFIG_FILENAME}" @ONLY
)

install(FILES
    "${CMAKE_CURRENT_BINARY_DIR}/${CMAKE_FILES_DIRECTORY}/${CRYPTOMINISAT5_CONFIG_FILENAME}"
    DESTINATION "${CRYPTOMINISAT5_INSTALL_CMAKE_DIR}"
)

# Install the export set for use with the install-tree
install(
    EXPORT ${CRYPTOMINISAT5_EXPORT_NAME}
    DESTINATION "${CRYPTOMINISAT5_INSTALL_CMAKE_DIR}"
)
