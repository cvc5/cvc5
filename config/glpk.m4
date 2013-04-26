# CVC4_CHECK_FOR_GLPK
# -------------------
# Look for glpk and link it in, but only if user requested.
AC_DEFUN([CVC4_CHECK_FOR_GLPK], [
AC_MSG_CHECKING([whether user requested glpk support])
LIBGLPK=
have_libglpk=0
GLPK_LIBS=
if test "$with_glpk" = no; then
  AC_MSG_RESULT([no, glpk disabled by user])
elif test "$with_glpk" = yes; then
  AC_MSG_RESULT([yes, glpk requested by user])

  dnl Try a bunch of combinations until something works :-/
  GLPK_LIBS=
  AC_CHECK_HEADER([glpk.h], [],
    [AC_MSG_FAILURE([cannot find glpk.h, the GLPK header!])])
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
    AC_MSG_FAILURE([cannot link against libglpk! (or it's too old, or can't get it to work)])
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
  LIBS="-lglpk $1"
  AC_LINK_IFELSE([AC_LANG_PROGRAM([#include <glpk.h>],
                                  [int i = lpx_get_int_parm(NULL, LPX_K_ITCNT)])],
    [GLPK_LIBS="-lglpk $1"],
    [])
  LIBS="$cvc4_save_LIBS"
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
  cvc4_save_LDFLAGS="$LDFLAGS"
  LDFLAGS="-static $LDFLAGS"
  LIBS="-lglpk $1"
  AC_LINK_IFELSE([AC_LANG_PROGRAM([#include <glpk.h>],
                                  [int i = lpx_get_int_parm(NULL, LPX_K_ITCNT)])],
    [GLPK_LIBS="-lglpk $1"],
    [])
  LIBS="$cvc4_save_LIBS"
  LDFLAGS="$cvc4_save_LDFLAGS"
  AC_LANG_POP([C++])
fi
])# CVC4_TRY_STATIC_GLPK_WITH
