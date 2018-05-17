# CVC4_CHECK_FOR_SYMFPU
# ------------------
# Look for symfpu and link it in, but only if user requested.
AC_DEFUN([CVC4_CHECK_FOR_SYMFPU], [
AC_MSG_CHECKING([whether user requested symfpu support])

have_symfpu_headers=0
if test "$with_symfpu" = no; then
  AC_MSG_RESULT([no, symfpu disabled by user])
elif test -n "$with_symfpu"; then
  AC_MSG_RESULT([yes, symfpu requested by user])
  AC_ARG_VAR(SYMFPU_HOME, [path to top level of symfpu source tree])
  AC_ARG_WITH(
    [symfpu-dir],
    AS_HELP_STRING(
      [--with-symfpu-dir=PATH],
      [path to top level of symfpu source tree]
    ),
    SYMFPU_HOME="$withval",
    [ if test -z "$SYMFPU_HOME" && ! test -e "$ac_abs_confdir/symfpu-CVC4/symfpu/core"; then
        AC_MSG_FAILURE([must give --with-symfpu-dir=PATH, define environment variable SYMFPU_HOME, or use contrib/get-symfpu to setup symfpu for CVC4!])
      fi
    ]
  )

  # Check if symfpu was installed via contrib/get-symfpu or SYMFPU_HOME or --with-symfpu-dir was set
  AC_MSG_CHECKING([whether symfpu was installed via contrib/get-symfpu])
  if test -z "$SYMFPU_HOME" && test -e "$ac_abs_confdir/symfpu-CVC4/symfpu/core"; then
    SYMFPU_HOME="$ac_abs_confdir/symfpu-CVC4"
    AC_MSG_RESULT([yes, $SYMFPU_HOME])
    have_symfpu_headers=1
  else
    AC_MSG_RESULT([no])
  fi
else
  AC_MSG_RESULT([no, user didn't request symfpu])
  with_symfpu=no
fi

])# CVC4_CHECK_FOR_SYMFPU
