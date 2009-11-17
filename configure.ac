#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.63])
AC_INIT([src/include/cvc4.h])
AC_CONFIG_AUX_DIR([config])
#AC_CONFIG_LIBOBJ_DIR([lib])
AC_CONFIG_MACRO_DIR([config])
AM_INIT_AUTOMAKE(cvc4, prerelease)
AC_CONFIG_HEADERS([config.h])
LT_INIT

AC_LIBTOOL_WIN32_DLL

# Checks for programs.
AC_PROG_CC
AC_PROG_CXX
AC_PROG_INSTALL
AC_PROG_LIBTOOL
AM_PROG_LEX
AC_PROG_YACC

AC_CHECK_PROG(DOXYGEN, doxygen, doxygen,)
if test "$DOXYGEN" = ''; then
  echo 'WARNING: documentation targets require doxygen.  Set your PATH appropriately or set DOXYGEN to point to a valid doxygen binary.'
fi

# Checks for libraries.
AC_CHECK_LIB(gmp, __gmpz_init, , [AC_MSG_ERROR([GNU MP not found, see http://gmplib.org/])])

# Checks for header files.

# Checks for typedefs, structures, and compiler characteristics.
AC_HEADER_STDBOOL
AC_TYPE_UINT16_T
AC_TYPE_UINT32_T
AC_TYPE_UINT64_T
AC_TYPE_SIZE_T

# Checks for library functions.

AC_CONFIG_FILES([
  Makefile
  contrib/Makefile
  doc/Makefile
  src/Makefile
  src/expr/Makefile
  src/smt/Makefile
  src/main/Makefile
  src/prop/minisat/Makefile
  src/prop/Makefile
  src/util/Makefile
  src/context/Makefile
  src/parser/Makefile
  src/theory/Makefile
])
AC_OUTPUT
