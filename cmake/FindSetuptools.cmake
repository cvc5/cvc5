###############################################################################
# Top contributors (to current version):
#   Daniel Larraz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find setuptools
# Setuptools_FOUND - found setuptools Python module
# Setuptools_VERSION - setuptools version
##

if (Setuptools_FIND_REQUIRED)
  set(Setuptools_FIND_MODE FATAL_ERROR)
else()
  set(Setuptools_FIND_MODE STATUS)
endif()

macro(get_setuptools_version)
  execute_process(
      COMMAND "${Python_EXECUTABLE}" -c "import setuptools; print(setuptools.__version__)"
      RESULT_VARIABLE Setuptools_VERSION_CHECK_RESULT
      OUTPUT_VARIABLE Setuptools_VERSION
      ERROR_QUIET
      OUTPUT_STRIP_TRAILING_WHITESPACE
  )
endmacro()

set(INSTALL_SETUPTOOLS FALSE)

get_setuptools_version()

if (Setuptools_VERSION_CHECK_RESULT EQUAL 0)
  set(Setuptools_FOUND TRUE)
  message(STATUS "Found setuptools version: ${Setuptools_VERSION}")
  if (DEFINED Setuptools_FIND_VERSION)
    if (Setuptools_FIND_VERSION_EXACT)
      if (NOT (Setuptools_VERSION VERSION_EQUAL ${Setuptools_FIND_VERSION}))
        set(INSTALL_SETUPTOOLS TRUE)
        set(INSTALL_SETUPTOOLS_OPTION "==${Setuptools_FIND_VERSION}")
        set(INSTALL_SETUPTOOLS_MESSAGE "==${Setuptools_FIND_VERSION}")
      endif()
    else()
      if (Setuptools_VERSION VERSION_LESS ${Setuptools_FIND_VERSION})
        set(INSTALL_SETUPTOOLS TRUE)
        set(INSTALL_SETUPTOOLS_OPTION ";-U")
        set(INSTALL_SETUPTOOLS_MESSAGE ">=${Setuptools_FIND_VERSION}")
      endif()
    endif()
    if (INSTALL_SETUPTOOLS AND NOT ENABLE_AUTO_DOWNLOAD)
      set(INSTALL_SETUPTOOLS FALSE)
      message(${Setuptools_FIND_MODE}
        "Setuptools version${INSTALL_SETUPTOOLS_MESSAGE} is required, "
        "but found version ${Setuptools_VERSION}.\n"
        "Use --auto-download to let us install it for you."
      )
    endif()
  endif()
else()
  set(Setuptools_FOUND FALSE)
  if (NOT ENABLE_AUTO_DOWNLOAD)
    message(${Setuptools_FIND_MODE}
      "Could NOT find the setuptools module. "
      "Use --auto-download to let us install it for you.")
  else()
    set(INSTALL_SETUPTOOLS TRUE)
    set(INSTALL_SETUPTOOLS_OPTION ";-U")
    set(INSTALL_SETUPTOOLS_MESSAGE "")
  endif()
endif()

if(INSTALL_SETUPTOOLS)
  if(WIN32)
    # Version 70.2.0 (the latest currently) triggers an error on Windows.
    # This is a workaround that installs the previous version.
    set(INSTALL_SETUPTOOLS_OPTION "==70.1.1")
    set(INSTALL_SETUPTOOLS_MESSAGE "==70.1.1")
  endif()
  message(STATUS "Installing setuptools${INSTALL_SETUPTOOLS_MESSAGE}")
  execute_process(
    COMMAND
    ${Python_EXECUTABLE} -m pip install setuptools${INSTALL_SETUPTOOLS_OPTION}
    RESULT_VARIABLE SETUPTOOLS_INSTALL_CMD_EXIT_CODE
  )
  if(SETUPTOOLS_INSTALL_CMD_EXIT_CODE)
    message(${Setuptools_FIND_MODE}
      "Could NOT install setuptools${INSTALL_SETUPTOOLS_MESSAGE}"
    )
  else()
    set(Setuptools_FOUND TRUE)
    get_setuptools_version()
  endif()
endif()
