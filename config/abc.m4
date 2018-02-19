# CVC4_CHECK_FOR_ABC
# ------------------
# Look for abc and link it in, but only if user requested.
AC_DEFUN([CVC4_CHECK_FOR_ABC], [
AC_MSG_CHECKING([whether user requested abc support])
LIBABC=
have_libabc=0
ABC_LIBS=
ABC_LDFLAGS=
if test "$with_abc" = no; then
  AC_MSG_RESULT([no, abc disabled by user])
elif test -n "$with_abc"; then
  AC_MSG_RESULT([yes, abc requested by user])

  # Get the location of all the ABC stuff
  AC_ARG_VAR(ABC_HOME, [path to top level of abc source tree])
  AC_ARG_WITH(
    [abc-dir],
    AS_HELP_STRING(
      [--with-abc-dir=PATH],
      [path to top level of abc source tree]
    ),
    [ABC_HOME="$withval"],
    [ if test -z "$ABC_HOME" && ! test -e "$ac_abs_confdir/abc/alanmi-abc-53f39c11b58d/arch_flags"; then
        AC_MSG_FAILURE([must give --with-abc-dir=PATH, define environment variable ABC_HOME, or use contrib/get-abc to setup ABC for CVC4!])
      fi
    ]
  )
  # Check if ABC was installed via contrib/get-abc
  AC_MSG_CHECKING([whether ABC was already installed via contrib/get-abc])
  if test -z "$ABC_HOME" && test -e "$ac_abs_confdir/abc/alanmi-abc-53f39c11b58d/arch_flags"; then
    ABC_HOME="$ac_abs_confdir/abc/alanmi-abc-53f39c11b58d"
    AC_MSG_RESULT([yes, $ABC_HOME])
  else
    AC_MSG_RESULT([no])
  fi

  if ! test -d "$ABC_HOME" || ! test -x "$ABC_HOME/arch_flags"; then
    AC_MSG_FAILURE([either $ABC_HOME is not an abc source tree or it's not yet built])
  fi

  AC_MSG_CHECKING([for arch_flags to use with libabc])
  libabc_arch_flags="$("$ABC_HOME/arch_flags")"
  AC_MSG_RESULT([$libabc_arch_flags])
  CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-I$ABC_HOME/src $libabc_arch_flags"
  ABC_LDFLAGS="-L$ABC_HOME"

  dnl Try a bunch of combinations until something works :-/
  cvc4_save_LDFLAGS="$LDFLAGS"
  ABC_LIBS=
  CPPFLAGS="$CPPFLAGS -I$ABC_HOME/src $libabc_arch_flags"
  LDFLAGS="$LDFLAGS $ABC_LDFLAGS"
  AC_CHECK_HEADER([base/abc/abc.h], [], [AC_MSG_FAILURE([cannot find abc.h, the ABC header!])])
  AC_MSG_CHECKING([how to link abc])
  CVC4_TRY_ABC_WITH([])
  CVC4_TRY_ABC_WITH([-lm])
  CVC4_TRY_ABC_WITH([-lm -lrt])
  CVC4_TRY_ABC_WITH([-lm -lrt -ldl])
  CVC4_TRY_ABC_WITH([-lm -lrt -lreadline -ldl])
  CVC4_TRY_ABC_WITH([-lm -lpthread])
  CVC4_TRY_ABC_WITH([-lm -lpthread -lrt])
  CVC4_TRY_ABC_WITH([-lm -lpthread -lrt -ldl])
  CVC4_TRY_ABC_WITH([-lm -lpthread -lrt -lreadline -ldl])
  dnl CVC4_TRY_ABC_WITH([-lm -rdynamic -lreadline -lpthread -lrt -ldl])
  if test -z "$ABC_LIBS"; then
    AC_MSG_FAILURE([cannot link against libabc!])
  else
    AC_MSG_RESULT([$ABC_LIBS])
    # make sure it works in static builds, too
    if test "$enable_static_binary" = yes; then
      ABC_LIBS=
      AC_MSG_CHECKING([whether statically-linked abc is functional])
      CVC4_TRY_STATIC_ABC_WITH([])
      CVC4_TRY_STATIC_ABC_WITH([-lm])
      CVC4_TRY_STATIC_ABC_WITH([-lm -lrt])
      CVC4_TRY_STATIC_ABC_WITH([-lm -lrt -ldl])
      CVC4_TRY_STATIC_ABC_WITH([-lm -lrt -lreadline -ldl])
      CVC4_TRY_STATIC_ABC_WITH([-lm -lpthread])
      CVC4_TRY_STATIC_ABC_WITH([-lm -lpthread -lrt])
      CVC4_TRY_STATIC_ABC_WITH([-lm -lpthread -lrt -ldl])
      CVC4_TRY_STATIC_ABC_WITH([-lm -lpthread -lrt -lreadline -ldl])
      if test -n "$ABC_LIBS"; then
        AC_MSG_RESULT([yes, it works])
        with_abc=yes
      else
        AC_MSG_RESULT([no])
        AC_MSG_FAILURE([abc installation appears incompatible with static-binary])
      fi
    else
      with_abc=yes
    fi
  fi
  if test "$with_abc" = yes; then
    have_libabc=1
  else
    with_abc=no
    have_libreadline=0
    ABC_LIBS=
  fi
  LDFLAGS="$cvc4_save_LDFLAGS"
else
  AC_MSG_RESULT([no, user didn't request abc])
  with_abc=no
fi
])# CVC4_CHECK_FOR_ABC

# CVC4_TRY_ABC_WITH(LIBS)
# -----------------------
# Try AC_CHECK_LIB(abc) with the given linking libraries
AC_DEFUN([CVC4_TRY_ABC_WITH], [
if test -z "$ABC_LIBS"; then
  AC_LANG_PUSH([C++])
  cvc4_save_LIBS="$LIBS"
  LIBS="-labc $1"
  AC_LINK_IFELSE([AC_LANG_PROGRAM([extern "C" { void Abc_Start(); }],
                                  [Abc_Start()])],
    [ABC_LIBS="-labc $1"],
    [])
  LIBS="$cvc4_save_LIBS"
  AC_LANG_POP([C++])
fi
])# CVC4_TRY_ABC_WITH

# CVC4_TRY_STATIC_ABC_WITH(LIBS)
# ------------------------------
# Try AC_CHECK_LIB(abc) with the given linking libraries
AC_DEFUN([CVC4_TRY_STATIC_ABC_WITH], [
if test -z "$ABC_LIBS"; then
  AC_LANG_PUSH([C++])
  cvc4_save_LIBS="$LIBS"
  cvc4_save_LDFLAGS="$LDFLAGS"
  LDFLAGS="-static $LDFLAGS"
  LIBS="-labc-static $1"
  AC_LINK_IFELSE([AC_LANG_PROGRAM([extern "C" { void Abc_Start(); }],
                                  [Abc_Start()])],
    [ABC_LIBS="-labc-static $1"],
    [ LIBS="-labc $1"
      AC_LINK_IFELSE([AC_LANG_PROGRAM([extern "C" { void Abc_Start(); }],
                                      [Abc_Start()])],
        [ABC_LIBS="-labc $1"]) ])
  LIBS="$cvc4_save_LIBS"
  LDFLAGS="$cvc4_save_LDFLAGS"
  AC_LANG_POP([C++])
fi
])# CVC4_TRY_STATIC_ABC_WITH
