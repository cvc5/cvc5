#####################
## FindCxxTest.cmake
## Top contributors (to current version):
##   Mathias Preiner, Alex Ozdemir, Andrew Reynolds
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
# Find CxxTest
# CxxTest_FOUND - system has CxxTest lib
# CxxTest_INCLUDE_DIR - the CxxTest include directory
# CxxTest_TESTGEN_EXECUTABLE - CxxTest excecutable
# CxxTest_TESTGEN_INTERPRETER - Python/Perl interpreter for running executable

find_package(PythonInterp QUIET)
find_package(Perl QUIET)

find_path(CxxTest_INCLUDE_DIR cxxtest/TestSuite.h
          PATHS ${CxxTest_HOME}
          NO_DEFAULT_PATH)
find_program(CxxTest_PYTHON_TESTGEN_EXECUTABLE
             NAMES cxxtestgen cxxtestgen.py
             PATHS ${CxxTest_HOME}/bin
             NO_DEFAULT_PATH)
find_program(CxxTest_PERL_TESTGEN_EXECUTABLE cxxtestgen.pl
             PATHS ${CxxTest_HOME}/bin
             NO_DEFAULT_PATH)

if(NOT CxxTest_HOME)
  find_path(CxxTest_INCLUDE_DIR cxxtest/TestSuite.h)
  find_program(CxxTest_PYTHON_TESTGEN_EXECUTABLE NAMES cxxtestgen.py)
  find_program(CxxTest_SHEBANG_TESTGEN_EXECUTABLE NAMES cxxtestgen)
  find_program(CxxTest_PERL_TESTGEN_EXECUTABLE cxxtestgen.pl)
endif()


if(CxxTest_SHEBANG_TESTGEN_EXECUTABLE)
  set(CxxTest_USE_SHEBANG ON)
  set(CxxTest_TESTGEN_EXECUTABLE ${CxxTest_SHEBANG_TESTGEN_EXECUTABLE})
elseif(PYTHONINTERP_FOUND AND CxxTest_PYTHON_TESTGEN_EXECUTABLE)
  set(CxxTest_TESTGEN_EXECUTABLE ${CxxTest_PYTHON_TESTGEN_EXECUTABLE})
  set(CxxTest_TESTGEN_INTERPRETER ${PYTHON_EXECUTABLE})
elseif(PERL_FOUND AND CxxTest_PERL_TESTGEN_EXECUTABLE)
  set(CxxTest_TESTGEN_EXECUTABLE ${CxxTest_PERL_TESTGEN_EXECUTABLE})
  set(CxxTest_TESTGEN_INTERPRETER ${PERL_EXECUTABLE})
elseif(NOT PYTHONINTERP_FOUND AND NOT PERL_FOUND AND CxxTest_FIND_REQUIRED)
  message(FATAL_ERROR "Neither Python nor Perl found, cannot use CxxTest.")
endif()

if(NOT DEFINED CxxTest_TESTGEN_ARGS)
  set(CxxTest_TESTGEN_ARGS --error-printer)
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(
  CxxTest DEFAULT_MSG CxxTest_INCLUDE_DIR CxxTest_TESTGEN_EXECUTABLE)

mark_as_advanced(CxxTest_INCLUDE_DIR CxxTest_TESTGEN_EXECUTABLE)
