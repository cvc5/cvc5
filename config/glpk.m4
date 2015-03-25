# CVC4_CHECK_FOR_GLPK
# -------------------
# Look for glpk and link it in, but only if user requested.
AC_DEFUN([CVC4_CHECK_FOR_GLPK], [
AC_MSG_CHECKING([whether user requested glpk support])
LIBGLPK=
have_libglpk=0
GLPK_LIBS=
GLPK_LDFLAGS=
if test "$with_glpk" = no; then
  AC_MSG_RESULT([no, glpk disabled by user])
elif test -n "$with_glpk"; then
  AC_MSG_RESULT([yes, glpk requested by user])

  # Get the location of all the GLPK stuff
  AC_ARG_VAR(GLPK_HOME, [path to top level of glpk installation])
  AC_ARG_WITH(
    [glpk-dir],
    AS_HELP_STRING(
      [--with-glpk-dir=PATH],
      [path to top level of glpk installation]
    ),
    [GLPK_HOME="$withval"],
    [ if test -z "$GLPK_HOME"; then
        AC_MSG_FAILURE([must give --with-glpk-dir=PATH or define environment variable GLPK_HOME!])
      fi
    ]
  )

  if test -n "$GLPK_HOME"; then
    CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-I$GLPK_HOME/include"
    GLPK_LDFLAGS="-L$GLPK_HOME/lib"
  fi

  dnl Try a bunch of combinations until something works :-/
  GLPK_LIBS=
  AC_LANG_PUSH([C++])
  cvc4_save_CPPFLAGS="$CPPFLAGS"
  CPPFLAGS="$CVC4CPPFLAGS $CPPFLAGS"
  AC_CHECK_HEADER([glpk.h], [], [AC_MSG_FAILURE([cannot find glpk.h, the GLPK header!])])
  CPPFLAGS="$cvc4_save_CPPFLAGS"
  AC_LANG_POP([C++])

  AC_MSG_CHECKING([how to link glpk])
  CVC4_TRY_GLPK_WITH([])
  CVC4_TRY_GLPK_WITH([-lgmp])
  CVC4_TRY_GLPK_WITH([-lz])
  CVC4_TRY_GLPK_WITH([-ldl])
  CVC4_TRY_GLPK_WITH([-lltdl])
  CVC4_TRY_GLPK_WITH([-lltdl -ldl])
  CVC4_TRY_GLPK_WITH([-lz -ldl])
  CVC4_TRY_GLPK_WITH([-lz -lltdl])
  CVC4_TRY_GLPK_WITH([-lz -lltdl -ldl])
  CVC4_TRY_GLPK_WITH([-lgmp -lz])
  CVC4_TRY_GLPK_WITH([-lgmp -ldl])
  CVC4_TRY_GLPK_WITH([-lgmp -lltdl])
  CVC4_TRY_GLPK_WITH([-lgmp -lltdl -ldl])
  CVC4_TRY_GLPK_WITH([-lgmp -lz -ldl])
  CVC4_TRY_GLPK_WITH([-lgmp -lz -lltdl])
  CVC4_TRY_GLPK_WITH([-lgmp -lz -lltdl -ldl])
  if test -z "$GLPK_LIBS"; then
    AC_MSG_FAILURE([cannot link against libglpk! (perhaps you have not switched to glpk-cut-log? see /INSTALL)])
  else
    AC_MSG_RESULT([$GLPK_LIBS])
    # make sure it works in static builds, too
    if test "$enable_static_binary" = yes; then
      GLPK_LIBS=
      AC_MSG_CHECKING([whether statically-linked glpk is functional])
      CVC4_TRY_STATIC_GLPK_WITH([])
      CVC4_TRY_STATIC_GLPK_WITH([-lgmp])
      CVC4_TRY_STATIC_GLPK_WITH([-lz])
      CVC4_TRY_STATIC_GLPK_WITH([-ldl])
      CVC4_TRY_STATIC_GLPK_WITH([-lltdl])
      CVC4_TRY_STATIC_GLPK_WITH([-lltdl -ldl])
      CVC4_TRY_STATIC_GLPK_WITH([-lz -ldl])
      CVC4_TRY_STATIC_GLPK_WITH([-lz -lltdl])
      CVC4_TRY_STATIC_GLPK_WITH([-lz -lltdl -ldl])
      CVC4_TRY_STATIC_GLPK_WITH([-lgmp -lz])
      CVC4_TRY_STATIC_GLPK_WITH([-lgmp -ldl])
      CVC4_TRY_STATIC_GLPK_WITH([-lgmp -lltdl])
      CVC4_TRY_STATIC_GLPK_WITH([-lgmp -lltdl -ldl])
      CVC4_TRY_STATIC_GLPK_WITH([-lgmp -lz -ldl])
      CVC4_TRY_STATIC_GLPK_WITH([-lgmp -lz -lltdl])
      CVC4_TRY_STATIC_GLPK_WITH([-lgmp -lz -lltdl -ldl])
      if test -n "$GLPK_LIBS"; then
        AC_MSG_RESULT([yes, it works])
        with_glpk=yes
      else
        AC_MSG_RESULT([no])
        AC_MSG_FAILURE([glpk installation appears incompatible with static-binary])
      fi
    else
      with_glpk=yes
    fi
  fi
  if test "$with_glpk" = yes; then
    have_libglpk=1
  else
    with_glpk=no
    have_libreadline=0
    GLPK_LIBS=
  fi
else
  AC_MSG_RESULT([no, user didn't request glpk])
  with_glpk=no
fi
])# CVC4_CHECK_FOR_GLPK

# CVC4_TRY_GLPK_WITH(LIBS)
# ------------------------
# Try AC_CHECK_LIB(glpk) with the given linking libraries
AC_DEFUN([CVC4_TRY_GLPK_WITH], [
if test -z "$GLPK_LIBS"; then
  AC_LANG_PUSH([C++])
  cvc4_save_LIBS="$LIBS"
  cvc4_save_CPPFLAGS="$CPPFLAGS"
  cvc4_save_LDFLAGS="$LDFLAGS"
  CPPFLAGS="$CVC4CPPFLAGS $CPPFLAGS"
  LDFLAGS="$GLPK_LDFLAGS $LDFLAGS"
  LIBS="-lglpk $1"
  AC_LINK_IFELSE([AC_LANG_PROGRAM([#include <glpk.h>],
                                  [int i = glp_ios_get_cut(NULL, 0, NULL, NULL, NULL, NULL, NULL)])],
    [GLPK_LIBS="-lglpk $1"],
    [])
  LIBS="$cvc4_save_LIBS"
  CPPFLAGS="$cvc4_save_CPPFLAGS"
  LDFLAGS="$cvc4_save_LDFLAGS"
  AC_LANG_POP([C++])
fi
])# CVC4_TRY_GLPK_WITH

# CVC4_TRY_STATIC_GLPK_WITH(LIBS)
# -------------------------------
# Try AC_CHECK_LIB(glpk) with the given linking libraries
AC_DEFUN([CVC4_TRY_STATIC_GLPK_WITH], [
if test -z "$GLPK_LIBS"; then
  AC_LANG_PUSH([C++])
  cvc4_save_LIBS="$LIBS"
  cvc4_save_CPPFLAGS="$CPPFLAGS"
  cvc4_save_LDFLAGS="$LDFLAGS"
  CPPFLAGS="$CVC4CPPFLAGS $CPPFLAGS"
  LDFLAGS="-static $GLPK_LDFLAGS $LDFLAGS"
  LIBS="-lglpk-static $1"
  AC_LINK_IFELSE([AC_LANG_PROGRAM([#include <glpk.h>],
                                  [int i = glp_ios_get_cut(NULL, 0, NULL, NULL, NULL, NULL, NULL)])],
    [GLPK_LIBS="-lglpk-static $1"],
    [ LIBS="-lglpk $1"
      AC_LINK_IFELSE([AC_LANG_PROGRAM([#include <glpk.h>],
                                      [int i = glp_ios_get_cut(NULL, 0, NULL, NULL, NULL, NULL, NULL)])],

        [GLPK_LIBS="-lglpk $1"]) ])
  LIBS="$cvc4_save_LIBS"
  CPPFLAGS="$cvc4_save_CPPFLAGS"
  LDFLAGS="$cvc4_save_LDFLAGS"
  AC_LANG_POP([C++])
fi
])# CVC4_TRY_STATIC_GLPK_WITH
