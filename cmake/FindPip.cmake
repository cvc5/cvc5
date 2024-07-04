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
# Find Pip
# Pip_FOUND - found Python pip
# Pip_VERSION - Python pip version
##

macro(get_pip_version)
  execute_process(
    COMMAND "${Python_EXECUTABLE}" -c "import pip; print(pip.__version__)"
    RESULT_VARIABLE Pip_VERSION_CHECK_RESULT
    OUTPUT_VARIABLE Pip_VERSION
    ERROR_QUIET
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )
endmacro()

get_pip_version()

if (Pip_FIND_REQUIRED)
  set(Pip_FIND_MODE FATAL_ERROR)
else()
  set(Pip_FIND_MODE STATUS)
endif()

if(Pip_VERSION_CHECK_RESULT EQUAL 0)
  set(Pip_FOUND TRUE)
  if(DEFINED Pip_FIND_VERSION)
    if(Pip_VERSION VERSION_LESS ${Pip_FIND_VERSION})
      if(ENABLE_AUTO_DOWNLOAD)
        execute_process (
          COMMAND "${Python_EXECUTABLE}" -m pip install -U pip
        )
        get_pip_version()
      else()
        message(${Pip_FIND_MODE}
          "Pip version >= ${Pip_FIND_VERSION} is required, "
          "but found version ${Pip_VERSION}")
      endif()
    endif()
  endif()
else()
  set(Pip_FOUND FALSE)
  if(ENABLE_AUTO_DOWNLOAD)
    execute_process (
      COMMAND "${Python_EXECUTABLE}" -m ensurepip --upgrade
      RESULT_VARIABLE ENSUREPIP_RESULT
    )
    if (ENSUREPIP_RESULT EQUAL 0)
      set(Pip_FOUND TRUE)
    else()
      message(${Pip_FIND_MODE} "Could NOT install pip for Python version "
        "${Python_VERSION_MAJOR}.${Python_VERSION_MINOR}")
    endif()
  else()
    message(${Pip_FIND_MODE} "Could NOT find pip for Python version "
      "${Python_VERSION_MAJOR}.${Python_VERSION_MINOR}")
  endif()
endif()