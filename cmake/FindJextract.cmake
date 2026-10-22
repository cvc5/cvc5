###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find jextract, which generates the Java bindings of the C API for the
# Foreign Function & Memory API (https://github.com/openjdk/jextract).
# Jextract_FOUND      - jextract was found or downloaded
# JEXTRACT_EXECUTABLE - the jextract launcher
##

include(deps-helper)

# The distribution contains a shell script and a batch file.
if(CMAKE_HOST_WIN32)
  set(JEXTRACT_NAMES jextract.bat)
else()
  set(JEXTRACT_NAMES jextract)
endif()

find_program(JEXTRACT_EXECUTABLE
  NAMES ${JEXTRACT_NAMES}
  HINTS ${JEXTRACT_HOME} $ENV{JEXTRACT_HOME} ${DEPS_BASE}/jextract
  PATH_SUFFIXES bin
)

set(Jextract_FOUND_SYSTEM FALSE)
if(JEXTRACT_EXECUTABLE)
  set(Jextract_FOUND_SYSTEM TRUE)
else()
  check_auto_download("Jextract" "")

  set(JEXTRACT_VERSION "25-jextract+2-4")
  set(JEXTRACT_URL "https://download.java.net/java/early_access/jextract/25/2")
  string(TOLOWER "${CMAKE_HOST_SYSTEM_PROCESSOR}" _jextract_arch)
  if(CMAKE_HOST_WIN32)
    # There is no build for Windows on ARM64 yet. The x64 build runs on ARM64
    # through the x64 emulation of Windows.
    set(_jextract_platform "windows-x64")
    set(_jextract_sha256
      "b03533eb6b249a154752b7c7bf93cdb8c147cf2f9699422e615e84b7fb652872")
  elseif(CMAKE_HOST_APPLE AND _jextract_arch MATCHES "arm64|aarch64")
    set(_jextract_platform "macos-aarch64")
    set(_jextract_sha256
      "3dd1dd1bde059d271739e2cc2290c64f93f85488c86c01e566c0e374eece798f")
  elseif(CMAKE_HOST_APPLE)
    set(_jextract_platform "macos-x64")
    set(_jextract_sha256
      "6ae7a46e7e7b56f077ab72623c0a894a8d525d5b698c90785b97c241f95a99b1")
  elseif(_jextract_arch MATCHES "arm64|aarch64")
    set(_jextract_platform "linux-aarch64")
    set(_jextract_sha256
      "0e25e6f6efa042f8758eaec65a873887fd2247fcf2e3e22dcfd7e4179fc8b0ae")
  else()
    set(_jextract_platform "linux-x64")
    set(_jextract_sha256
      "d0cc481abc1adb16fb9514e1c5e0bfc08d38c29228bece667fb5054ceaffaa42")
  endif()

  # jextract is needed at configure time, since the Java API is configured with
  # the files that it generates.
  set(_jextract_archive
    "${DEPS_BASE}/src/openjdk-${JEXTRACT_VERSION}_${_jextract_platform}_bin.tar.gz")
  message(STATUS "Downloading jextract ${JEXTRACT_VERSION} (${_jextract_platform})")
  file(DOWNLOAD
    "${JEXTRACT_URL}/openjdk-${JEXTRACT_VERSION}_${_jextract_platform}_bin.tar.gz"
    "${_jextract_archive}"
    EXPECTED_HASH SHA256=${_jextract_sha256}
    STATUS _jextract_status
  )
  list(GET _jextract_status 0 _jextract_error)
  if(_jextract_error)
    message(FATAL_ERROR "Could not download jextract: ${_jextract_status}")
  endif()
  file(REMOVE_RECURSE "${DEPS_BASE}/src/jextract-25" "${DEPS_BASE}/jextract")
  execute_process(
    COMMAND ${CMAKE_COMMAND} -E tar xzf "${_jextract_archive}"
    WORKING_DIRECTORY "${DEPS_BASE}/src"
    RESULT_VARIABLE _jextract_error
  )
  if(_jextract_error)
    message(FATAL_ERROR "Could not extract jextract from ${_jextract_archive}")
  endif()
  file(RENAME "${DEPS_BASE}/src/jextract-25" "${DEPS_BASE}/jextract")
  find_program(JEXTRACT_EXECUTABLE
    NAMES ${JEXTRACT_NAMES}
    PATHS ${DEPS_BASE}/jextract/bin
    NO_DEFAULT_PATH
  )
  if(NOT JEXTRACT_EXECUTABLE)
    message(FATAL_ERROR "Could not find jextract in ${DEPS_BASE}/jextract/bin")
  endif()
endif()

set(Jextract_FOUND TRUE)

mark_as_advanced(JEXTRACT_EXECUTABLE)
mark_as_advanced(Jextract_FOUND)

if(Jextract_FOUND_SYSTEM)
  message(STATUS "Found jextract: ${JEXTRACT_EXECUTABLE}")
else()
  message(STATUS "Using downloaded jextract: ${JEXTRACT_EXECUTABLE}")
endif()
