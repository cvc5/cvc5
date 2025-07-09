###############################################################################
# Top contributors (to current version):
#   Daniel Larraz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find Sphinx
# Sphinx_FOUND - system has the sphinx-build executable
# Sphinx_EXECUTABLE - path to the sphinx-build executable
# Sphinx_VERSION - Sphinx version
##

include(python-scripts-paths)
# Defines the Python_SCRIPTS_Paths variable with
# a list of Python "Scripts" directories
collect_python_scripts_paths()

if (Sphinx_FIND_REQUIRED)
  set(Sphinx_FIND_MODE FATAL_ERROR)
else()
  set(Sphinx_FIND_MODE STATUS)
endif()

macro(get_sphinx_version)
  find_program(Sphinx_EXECUTABLE sphinx-build ${Python_SCRIPTS_Paths})
  if(Sphinx_EXECUTABLE)
    execute_process(
      COMMAND "${Sphinx_EXECUTABLE}" --version
      RESULT_VARIABLE Sphinx_VERSION_CHECK_RESULT
      OUTPUT_VARIABLE Sphinx_VERSION
      ERROR_QUIET
    )
  else()
    set(Sphinx_VERSION_CHECK_RESULT 127) # Not-found exit code
  endif()
endmacro()

set(INSTALL_SPHINX FALSE)

get_sphinx_version()

if (Sphinx_VERSION_CHECK_RESULT EQUAL 0)
  set(Sphinx_FOUND TRUE)
  message(STATUS "Found Sphinx version: ${Sphinx_VERSION}")
  if (DEFINED Sphinx_FIND_VERSION)
    if (Sphinx_FIND_VERSION_EXACT)
      if (NOT (Sphinx_VERSION VERSION_EQUAL ${Sphinx_FIND_VERSION}))
        set(INSTALL_SPHINX TRUE)
        set(INSTALL_SPHINX_OPTION "==${Sphinx_FIND_VERSION}")
        set(INSTALL_SPHINX_MESSAGE "==${Sphinx_FIND_VERSION}")
      endif()
    else()
      if (Sphinx_VERSION VERSION_LESS ${Sphinx_FIND_VERSION})
        set(INSTALL_SPHINX TRUE)
        set(INSTALL_SPHINX_OPTION ";-U")
        set(INSTALL_SPHINX_MESSAGE ">=${Sphinx_FIND_VERSION}")
      endif()
    endif()
    if (INSTALL_SPHINX AND NOT ENABLE_AUTO_DOWNLOAD)
      set(INSTALL_SPHINX FALSE)
      message(${Sphinx_FIND_MODE}
        "Sphinx version${INSTALL_SPHINX_MESSAGE} is required, "
        "but found version ${Sphinx_VERSION}.\n"
        "Use --auto-download to let us install it for you."
      )
    endif()
  endif()
else()
  set(Sphinx_FOUND FALSE)
  if (NOT ENABLE_AUTO_DOWNLOAD)
    message(${Sphinx_FIND_MODE}
      "Could NOT find sphinx-build executable. "
      "Use --auto-download to let us install it for you.")
  else()
    set(INSTALL_SPHINX TRUE)
    set(INSTALL_SPHINX_OPTION ";-U")
    set(INSTALL_SPHINX_MESSAGE "")
  endif()
endif()

if(INSTALL_SPHINX)
  message(STATUS "Installing sphinx${INSTALL_SPHINX_MESSAGE}")
  execute_process(
    COMMAND
    ${Python_EXECUTABLE} -m pip install sphinx${INSTALL_SPHINX_OPTION}
    RESULT_VARIABLE SPHINX_INSTALL_CMD_EXIT_CODE
  )
  if(SPHINX_INSTALL_CMD_EXIT_CODE)
    message(${Sphinx_FIND_MODE}
      "Could NOT install sphinx${INSTALL_SPHINX_MESSAGE}"
    )
  else()
    set(Sphinx_FOUND TRUE)
    get_sphinx_version()
  endif()
endif()
