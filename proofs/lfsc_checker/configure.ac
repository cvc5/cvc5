#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.61])
AC_INIT([lfsc-checker], [1.0], [cvc-bugs@cs.nyu.edu])
AC_CONFIG_SRCDIR([libwriter.h])
AC_CONFIG_AUX_DIR([config])
AC_CONFIG_MACRO_DIR([config])
AC_CONFIG_HEADERS([config.h])
AM_INIT_AUTOMAKE([1.11 foreign no-define tar-pax])
LT_INIT

AC_CANONICAL_BUILD
AC_CANONICAL_HOST
AC_CANONICAL_TARGET

m4_ifdef([AM_SILENT_RULES],[AM_SILENT_RULES([yes])])

# on by default
AM_MAINTAINER_MODE([enable])

# turn off static lib building by default
AC_ENABLE_SHARED
AC_DISABLE_STATIC

# Checks for programs.
AC_PROG_CXX
AC_PROG_CC

# Checks for libraries.
# FIXME: Replace `main' with a function in `-lgmp':
AC_CHECK_LIB([gmp], [__gmpz_init])

# Checks for header files.
AC_CHECK_HEADERS([stdlib.h string.h])

# Checks for typedefs, structures, and compiler characteristics.
AC_HEADER_STDBOOL
AC_C_INLINE
AC_TYPE_SIZE_T

# Checks for library functions.
AC_FUNC_MALLOC
AC_CHECK_FUNCS([strdup])

AC_CONFIG_FILES([Makefile])
AC_OUTPUT
