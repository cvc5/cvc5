###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Mathias Preiner, Andrew V. Jones
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Defines some initial setup for building the dependencies (paths and default
# options for external projects) and some helper functions and macros that are
# used in the custom FindX.cmake scripts.
##

# where to build dependencies
set(DEPS_PREFIX "${CMAKE_BINARY_DIR}/deps")
# base path to installed dependencies
set(DEPS_BASE "${CMAKE_BINARY_DIR}/deps")
# CMake wants directories specified via INTERFACE_SYSTEM_INCLUDE_DIRECTORIES
# (and similar) to exist when target property is set.
file(MAKE_DIRECTORY "${DEPS_BASE}/include/")

set(COMMON_EP_CONFIG
    PREFIX ${DEPS_PREFIX}
    LOG_DOWNLOAD ON
    LOG_UPDATE ON
    LOG_CONFIGURE ON
    LOG_BUILD ON
    LOG_INSTALL ON
)
if(CMAKE_VERSION VERSION_GREATER_EQUAL "3.14")
    set(COMMON_EP_CONFIG ${COMMON_EP_CONFIG}
        LOG_PATCH ON
        LOG_MERGED_STDOUTERR ON
        LOG_OUTPUT_ON_FAILURE ON
    )
endif()

# On Windows, we need to have a shell interpreter to call 'configure'
if(CMAKE_SYSTEM_NAME STREQUAL "Windows")
    find_program (SHELL "sh" REQUIRED)
    message(STATUS "Found shell interpreter: ${SHELL}")
else()
    set(SHELL "")
endif()

macro(force_static_library)
    if (WIN32)
        set(CMAKE_FIND_LIBRARY_SUFFIXES .lib .a)
    else()
        set(CMAKE_FIND_LIBRARY_SUFFIXES .a)
    endif()
endmacro(force_static_library)

macro(reset_force_static_library)
    if (WIN32)
        set(CMAKE_FIND_LIBRARY_SUFFIXES .dll .lib)
    else()
        set(CMAKE_FIND_LIBRARY_SUFFIXES .so .dylib .a)
    endif()
endmacro(reset_force_static_library)

macro(check_auto_download name disable_option)
    if(NOT ENABLE_AUTO_DOWNLOAD)
        if (${name}_FIND_VERSION)
            set(depname "${name} (>= ${${name}_FIND_VERSION})")
        else()
            set(depname "${name}")
        endif()
        if("${disable_option}" STREQUAL "")
            message(FATAL_ERROR "Could not find the required dependency \
${depname} in the system. Please install it yourself or use --auto-download to \
let us download and build it for you.")
        else()
            message(FATAL_ERROR "Could not find the optional dependency \
${depname} in the system. You can disable this dependency with \
${disable_option}, install it yourself or use --auto-download to let us \
download and build it for you.")
        endif()
    endif()
endmacro(check_auto_download)

# Check if the given external project was already set up in a previous
# configure call.
macro(check_ep_downloaded name)
  if(EXISTS "${DEPS_PREFIX}/src/${name}")
    set(${name}_DOWNLOADED TRUE)
  else()
    set(${name}_DOWNLOADED FALSE)
  endif()
endmacro()

macro(check_system_version name)
    # find_package sets this variable when called with a version
    # https://cmake.org/cmake/help/latest/command/find_package.html#version-selection
    # we ignore the EXACT option and version ranges here
    if (${name}_FIND_VERSION)
        if(${name}_VERSION VERSION_LESS ${name}_FIND_VERSION)
            message(VERBOSE "System version for ${name} has incompatible \
version: required ${${name}_FIND_VERSION} but found ${${name}_VERSION}")
            set(${name}_FOUND_SYSTEM FALSE)
        endif()
    endif()
endmacro(check_system_version)

# fail if we are cross compiling as indicated by name and processor
# we are cross compiling if
# - CMAKE_SYSTEM_NAME has been changed to ${name}
# - CMAKE_SYSTEM_PROCESSOR has been changed to ${processor}
function(check_if_cross_compiling OUT name processor)
    if(NOT "${CMAKE_SYSTEM_NAME}" STREQUAL "${CMAKE_HOST_SYSTEM_NAME}")
        if(NOT "${name}" STREQUAL "")
            if("${CMAKE_SYSTEM_NAME}" STREQUAL "${name}")
                set(${OUT} TRUE PARENT_SCOPE)
                return()
            endif()
        endif()
    endif()
    if(NOT "${CMAKE_SYSTEM_PROCESSOR}" STREQUAL "${CMAKE_HOST_SYSTEM_PROCESSOR}")
        if(NOT "${processor}" STREQUAL "")
            if("${CMAKE_SYSTEM_PROCESSOR}" STREQUAL "${processor}")
                set(${OUT} TRUE PARENT_SCOPE)
                return()
            endif()
        endif()
    endif()
    set(${OUT} FALSE PARENT_SCOPE)
endfunction(check_if_cross_compiling)

# fail if we are cross compiling as indicated by name and processor
# we are cross compiling if
# - CMAKE_SYSTEM_NAME has been changed to ${name}
# - CMAKE_SYSTEM_PROCESSOR has been changed to ${processor}
function(fail_if_cross_compiling name processor target error)
    check_if_cross_compiling(FAIL "${name}" "${processor}")
    if(FAIL)
        message(SEND_ERROR
        "We are cross compiling from \
${CMAKE_HOST_SYSTEM_NAME}-${CMAKE_HOST_SYSTEM_PROCESSOR} to \
${CMAKE_SYSTEM_NAME}-${CMAKE_SYSTEM_PROCESSOR}.\n"
        "This is not supported by ${target}:\n"
        "${error}")
    endif()
endfunction(fail_if_cross_compiling)

function(fail_if_include_missing include target)
    include(CheckIncludeFileCXX)
    check_include_file_cxx(${include} HAVE_INCLUDE)
    if(NOT HAVE_INCLUDE)
        message(SEND_ERROR "${target} requires ${include} header, but it is not available.")
    endif()
endfunction(fail_if_include_missing)
