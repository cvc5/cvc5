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

set(Python_SCRIPTS_Paths "")

macro(add_scripts_path python_bin scheme)
  execute_process(
    COMMAND "${python_bin}" -c 
      "import sysconfig; print(sysconfig.get_paths('${scheme}')['scripts'])"
    RESULT_VARIABLE Python_SCRIPTS_RESULT
    OUTPUT_VARIABLE Python_SCRIPTS
    ERROR_QUIET
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )
  if (NOT Python_SCRIPTS_RESULT AND Python_SCRIPTS)
    list(APPEND Python_SCRIPTS_Paths ${Python_SCRIPTS})
  endif()
endmacro()

macro(collect_python_scripts_paths)
  set(Python_SCRIPTS_Paths "") # Clear previously defined paths if any
  add_scripts_path("${Python_EXECUTABLE}" "posix_prefix")
  add_scripts_path("${Python_BASE_EXECUTABLE}" "posix_user")
  add_scripts_path("${Python_BASE_EXECUTABLE}" "posix_prefix")
  if(WIN32)
    add_scripts_path("${Python_EXECUTABLE}" "nt")
    add_scripts_path("${Python_BASE_EXECUTABLE}" "nt_user")
    add_scripts_path("${Python_BASE_EXECUTABLE}" "nt")
  endif()
endmacro()
