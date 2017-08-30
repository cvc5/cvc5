# CVC4_CHECK_FOR_LFSC
# ------------------
# Look for LFSC and link it in, but only if user requested.
AC_DEFUN([CVC4_CHECK_FOR_LFSC], [
AC_MSG_CHECKING([whether user requested LFSC support])

have_liblfsc=0
LFSC_LIBS=
LFSC_LDFLAGS=

have_liblfsc=0
if test "$with_lfsc" = no; then
  AC_MSG_RESULT([no, LFSC disabled by user])
elif test -n "$with_lfsc"; then
  AC_MSG_RESULT([yes, LFSC requested by user])
  AC_ARG_VAR(LFSC_HOME, [path to top level of LFSC source tree])
  AC_ARG_WITH(
    [lfsc-dir],
    AS_HELP_STRING(
      [--with-lfsc-dir=PATH],
      [path to top level of lfsc source tree]
    ),
    [LFSC_HOME="$withval"],
    []
  )

  if test -z "$LFSC_HOME" -a -e "$ac_abs_confdir/lfsc-checker"; then
    AC_MSG_CHECKING([for LFSC checker library])
    LFSC_HOME="$ac_abs_confdir/lfsc-checker/install"
    AC_MSG_RESULT([found LFSC checker in $LFSC_HOME])
  fi
  
  if test -z "$LFSC_HOME"; then
    AC_MSG_FAILURE([must give --with-lfsc-dir=PATH or define environment variable LFSC_HOME!])
  fi

  if ! test -d "$LFSC_HOME" || ! test -x "$LFSC_HOME/bin/lfscc" ; then
    AC_MSG_FAILURE([either $LFSC_HOME is not a LFSC install tree or it's not yet built])
  fi

  CPPFLAGS="$CPPFLAGS -I$LFSC_HOME/include"

  AC_MSG_CHECKING([how to link LFSC])
  CVC4_TRY_LFSC_LIB

  if test -z "$LFSC_LIBS"; then
    AC_MSG_FAILURE([cannot link against liblfscc!])
  else
    AC_MSG_RESULT([$LFSC_LIBS])
    have_liblfsc=1
  fi

  LFSC_LDFLAGS="-L$LFSC_HOME/lib"

else
  AC_MSG_RESULT([no, user didn't request LFSC])
  with_lfsc=no
fi

])# CVC4_CHECK_FOR_LFSC

# CVC4_TRY_LFSC_LIB
# ------------------------------
# Try AC_CHECK_LIB(lfsc) with the given linking libraries
AC_DEFUN([CVC4_TRY_LFSC_LIB], [
  AC_LANG_PUSH([C++])

  cvc4_save_LIBS="$LIBS"
  cvc4_save_LDFLAGS="$LDFLAGS"
  cvc4_save_CPPFLAGS="$CPPFLAGS"

  LDFLAGS="-L$LFSC_HOME/lib"
  LIBS="-llfscc -lgmp"

  AC_LINK_IFELSE(
    [AC_LANG_PROGRAM([[#include <lfscc.h>]], [[lfscc_init()]])],
    [LFSC_LIBS="-llfscc -lgmp"],
    [LFSC_LIBS=])

  LDFLAGS="$cvc4_save_LDFLAGS"
  CPPFLAGS="$cvc4_save_CPPFLAGS"
  LIBS="$cvc4_save_LIBS"

  AC_LANG_POP([C++])
])# CVC4_TRY_LFSC_LIB
