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

# Features requested by the user
AC_MSG_CHECKING([whether to do a debug build of CVC4])
AC_ARG_ENABLE([debug],      [AS_HELP_STRING([--enable-debug]      ,[do a debug build of CVC4])])
if test -z "${enable_debug+set}"; then
  enable_debug=no
fi
AC_MSG_RESULT([$enable_debug])

AC_MSG_CHECKING([whether to include assertions in build])
AC_ARG_ENABLE([assertions], [AS_HELP_STRING([--disable-assertions],[turn off assertions in build])])
if test -z "${enable_assertions+set}"; then
  enable_assertions=yes
fi
AC_MSG_RESULT([$enable_assertions])

if test "$enable_assertions" = no -a "$enable_debug" = yes; then
  AC_MSG_FAILURE([when debugging is on, so must assertions be.])
fi

# Checks for programs.
AC_PROG_CC
AC_PROG_CXX
AC_PROG_INSTALL
AC_PROG_LIBTOOL
AM_PROG_LEX
AC_PROG_YACC

AC_CHECK_PROG(DOXYGEN, doxygen, doxygen, [])
if test -z "$DOXYGEN"; then
  AC_MSG_WARN([documentation targets require doxygen.  Set your PATH appropriately or set DOXYGEN to point to a valid doxygen binary.])
fi

# Checks for libraries.
AC_CHECK_LIB(gmp, __gmpz_init, , [AC_MSG_ERROR([GNU MP not found, see http://gmplib.org/])])

# Checks for header files.
AC_CHECK_HEADERS([getopt.h unistd.h])

# Checks for typedefs, structures, and compiler characteristics.
AC_HEADER_STDBOOL
AC_TYPE_UINT16_T
AC_TYPE_UINT32_T
AC_TYPE_UINT64_T
AC_TYPE_SIZE_T

# Checks for library functions.

# Some definitions for config.h
if test "$enable_debug" = yes; then
  AC_DEFINE([CVC4_DEBUG], [], [Whether or not to include debugging code.])
fi

if test "$enable_assertions" = yes; then
  AC_DEFINE([CVC4_ASSERTIONS], [], [Whether or not assertions are enabled.])
fi

# Prepare configure output

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

# Final information to the user
debug=debug
if test "$enable_debug" = no; then
  debug=non-debug
fi
withassertions=with
if test "$enable_assertions" = no; then
  withassertions=without
fi

cat <<EOF

CVC4 $VERSION will be built as a $debug build $withassertions assertions.

Now just type make, followed by make check or make install, as you like.

EOF
