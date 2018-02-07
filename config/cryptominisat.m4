# CVC4_CHECK_FOR_CRYPTOMINISAT
# ------------------
# Look for cryptominisat and link it in, but only if user requested.
AC_DEFUN([CVC4_CHECK_FOR_CRYPTOMINISAT], [
AC_MSG_CHECKING([whether user requested cryptominisat support])

have_libcryptominisat=0
CRYPTOMINISAT_LIBS=
CRYPTOMINISAT_LDFLAGS=

have_libcryptominisat=0
if test "$with_cryptominisat" = no; then
  AC_MSG_RESULT([no, cryptominisat disabled by user])
elif test -n "$with_cryptominisat"; then
  AC_MSG_RESULT([yes, cryptominisat requested by user])
  AC_ARG_VAR(CRYPTOMINISAT_HOME, [path to top level of cryptominisat source tree])
  AC_ARG_WITH(
    [cryptominisat-dir],
    AS_HELP_STRING(
      [--with-cryptominisat-dir=PATH],
      [path to top level of cryptominisat source tree]
    ),
    CRYPTOMINISAT_HOME="$withval",
    [ if test -z "$CRYPTOMINISAT_HOME" && ! test -e "$ac_abs_confdir/cryptominisat4/install/bin/cryptominisat"; then
        AC_MSG_FAILURE([must give --with-cryptominisat-dir=PATH, define environment variable CRYPTOMINISAT_HOME, or use contrib/get-cryptominisat4 to setup Cryptominisat4 for CVC4!])
      fi
    ]
  )

  # Check if cryptominisat4 was installed via contrib/get-cryptominisat4
  AC_MSG_CHECKING([whether Cryptominisat4 was already installed via contrib/get-cryptominisat4])
  if test -z "$CRYPTOMINISAT_HOME" && test -e "$ac_abs_confdir/cryptominisat4/install/bin/cryptominisat"; then
    CRYPTOMINISAT_HOME="$ac_abs_confdir/cryptominisat4"
    AC_MSG_RESULT([yes, $CRYPTOMINISAT_HOME])
  else
    AC_MSG_RESULT([no])
  fi

  if ! test -d "$CRYPTOMINISAT_HOME" || ! test -x "$CRYPTOMINISAT_HOME/install/bin/cryptominisat" ; then
    AC_MSG_FAILURE([either $CRYPTOMINISAT_HOME is not an cryptominisat install tree or it's not yet built])
  fi

  CPPFLAGS="$CPPFLAGS -I$CRYPTOMINISAT_HOME/install/include"

  AC_MSG_CHECKING([how to link cryptominisat])

  dnl TODO FIXME:
  dnl For some reason the CVC4_TRY_CRYPTOMINISAT is not working correctly
  CVC4_TRY_CRYPTOMINISAT_WITH([-pthread])
  CVC4_TRY_CRYPTOMINISAT_WITH([-pthread -lm4ri])

  if test -z "$CRYPTOMINISAT_LIBS"; then
    AC_MSG_FAILURE([cannot link against libcryptominisat!])
  else
    AC_MSG_RESULT([$CRYPTOMINISAT_LIBS])
    have_libcryptominisat=1
  fi

  CRYPTOMINISAT_LDFLAGS="-L$CRYPTOMINISAT_HOME/install/lib"

else
  AC_MSG_RESULT([no, user didn't request cryptominisat])
  with_cryptominisat=no
fi

])# CVC4_CHECK_FOR_CRYPTOMINISAT

# CVC4_TRY_STATIC_CRYPTOMINISAT_WITH(LIBS)
# ------------------------------
# Try AC_CHECK_LIB(cryptominisat) with the given linking libraries
AC_DEFUN([CVC4_TRY_CRYPTOMINISAT_WITH], [
if test -z "$CRYPTOMINISAT_LIBS"; then
  AC_LANG_PUSH([C++])

  cvc4_save_LIBS="$LIBS"
  cvc4_save_LDFLAGS="$LDFLAGS"
  cvc4_save_CPPFLAGS="$CPPFLAGS"

  LDFLAGS="-L$CRYPTOMINISAT_HOME/install/lib"
  LIBS="-lcryptominisat4 $1"

  AC_LINK_IFELSE(
    [AC_LANG_PROGRAM([[#include <cryptominisat4/cryptominisat.h>]],
      [[CMSat::SATSolver test()]])], [CRYPTOMINISAT_LIBS="-lcryptominisat4 $1"],
    [CRYPTOMINISAT_LIBS=])

  LDFLAGS="$cvc4_save_LDFLAGS"
  CPPFLAGS="$cvc4_save_CPPFLAGS"
  LIBS="$cvc4_save_LIBS"

  AC_LANG_POP([C++])
fi
])# CVC4_TRY_CRYPTOMINISAT_WITH

