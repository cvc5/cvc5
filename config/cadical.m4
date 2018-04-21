# CVC4_CHECK_FOR_CADICAL
# ------------------
# Look for CaDiCaL and link it in, but only if user requested.
AC_DEFUN([CVC4_CHECK_FOR_CADICAL], [
AC_MSG_CHECKING([whether user requested CaDiCaL support])

have_libcadical=0
CADICAL_LIBS=
CADICAL_LDFLAGS=

have_libcadical=0
if test "$with_cadical" = no; then
  AC_MSG_RESULT([no, CaDiCaL disabled by user])
elif test -n "$with_cadical"; then
  AC_MSG_RESULT([yes, CaDiCaL requested by user])
  AC_ARG_VAR(CADICAL_HOME, [path to top level of CaDiCaL source tree])
  AC_ARG_WITH(
    [cadical-dir],
    AS_HELP_STRING(
      [--with-cadical-dir=PATH],
      [path to top level of CaDiCaL source tree]
    ),
    CADICAL_HOME="$withval",
    [ if test -z "$CADICAL_HOME" && ! test -e "$ac_abs_confdir/cadical/build/libcadical.a"; then
        AC_MSG_FAILURE([must give --with-cadical-dir=PATH, define environment variable CADICAL_HOME, or use contrib/get-cadical to setup CaDiCaL for CVC4!])
      fi
    ]
  )

  # Check if CaDiCaL was installed via contrib/get-cadical
  AC_MSG_CHECKING([whether CaDiCaL was already installed via contrib/get-cadical])
  if test -z "$CADICAL_HOME" && test -e "$ac_abs_confdir/cadical/build/libcadical.a"; then
    CADICAL_HOME="$ac_abs_confdir/cadical"
    AC_MSG_RESULT([yes, $CADICAL_HOME])
  else
    AC_MSG_RESULT([no])
  fi

  if ! test -d "$CADICAL_HOME" || ! test -e "$CADICAL_HOME/build/libcadical.a" ; then
    AC_MSG_FAILURE([either $CADICAL_HOME is not a CaDiCaL source tree or it's not yet built $CADICAL_HOME/build/libcadical.a])
  fi

  AC_MSG_CHECKING([how to link CaDiCaL])

  CVC4_TRY_CADICAL

  if test -z "$CADICAL_LIBS"; then
    AC_MSG_FAILURE([cannot link against libcadical!])
  else
    AC_MSG_RESULT([$CADICAL_LIBS])
    have_libcadical=1
  fi

  CADICAL_LDFLAGS="-L$CADICAL_HOME/build"

else
  AC_MSG_RESULT([no, user didn't request CaDiCaL])
  with_cadical=no
fi

])# CVC4_CHECK_FOR_CADICAL

# CVC4_TRY_CADICAL
# ------------------------------
# Try AC_CHECK_LIB(cadical) with the given linking libraries
AC_DEFUN([CVC4_TRY_CADICAL], [
if test -z "$CADICAL_LIBS"; then
  AC_LANG_PUSH([C++])

  cvc4_save_LIBS="$LIBS"
  cvc4_save_LDFLAGS="$LDFLAGS"
  cvc4_save_CPPFLAGS="$CPPFLAGS"

  LDFLAGS="-L$CADICAL_HOME/build"
  CPPFLAGS="$CPPFLAGS -I$CADICAL_HOME/src"
  LIBS="-lcadical"

  AC_LINK_IFELSE(
    [AC_LANG_PROGRAM([[#include <cadical.hpp>]],
      [[CaDiCaL::Solver test();]])], [CADICAL_LIBS="-lcadical"],
    [CADICAL_LIBS=])

  LDFLAGS="$cvc4_save_LDFLAGS"
  CPPFLAGS="$cvc4_save_CPPFLAGS"
  LIBS="$cvc4_save_LIBS"

  AC_LANG_POP([C++])
fi
])# CVC4_TRY_CADICAL

