# CVC4_CHECK_FOR_READLINE
# -----------------------
# Look for readline and link it in, but allow user to disable.
AC_DEFUN([CVC4_CHECK_FOR_READLINE], [
AC_MSG_CHECKING([whether user requested readline support])
LIBREADLINE=
have_libreadline=0
readline_compentry_func_returns_charp=0
READLINE_LIBS=
if test "$with_readline" = no; then
  AC_MSG_RESULT([no, readline disabled by user])
elif test "$with_readline" = check -a "$CVC4_BSD_LICENSED_CODE_ONLY" = 1; then
  AC_MSG_RESULT([no, using BSD-compatible dependences only])
  with_readline=no
else
  if test "$with_readline" = check; then
    AC_MSG_RESULT([no preference by user, will auto-detect])
  else
    AC_MSG_RESULT([yes, readline enabled by user])
  fi
  dnl Try a bunch of combinations until something works :-/
  READLINE_LIBS=
  CVC4_TRY_READLINE_WITH([])
  CVC4_TRY_READLINE_WITH([-ltinfo])
  CVC4_TRY_READLINE_WITH([-ltermcap])
  CVC4_TRY_READLINE_WITH([-ltermcap -ltinfo])
  CVC4_TRY_READLINE_WITH([-lncurses -ltermcap])
  CVC4_TRY_READLINE_WITH([-lncurses -ltermcap -ltinfo])
  CVC4_TRY_READLINE_WITH([-lcurses -ltermcap])
  CVC4_TRY_READLINE_WITH([-lcurses -ltermcap -ltinfo])
  if test -z "$READLINE_LIBS"; then
    if test "$with_readline" != check; then
      AC_MSG_FAILURE([cannot find libreadline! (or can't get it to work)])
    fi
    with_readline=no
  else
    # make sure it works in static builds, too
    if test "$enable_static_binary" = yes; then
      READLINE_LIBS=
      AC_MSG_CHECKING([whether statically-linked readline is functional])
      CVC4_TRY_STATIC_READLINE_WITH([])
      CVC4_TRY_STATIC_READLINE_WITH([-ltinfo])
      CVC4_TRY_STATIC_READLINE_WITH([-ltermcap])
      CVC4_TRY_STATIC_READLINE_WITH([-ltermcap -ltinfo])
      CVC4_TRY_STATIC_READLINE_WITH([-lncurses -ltermcap])
      CVC4_TRY_STATIC_READLINE_WITH([-lncurses -ltermcap -ltinfo])
      CVC4_TRY_STATIC_READLINE_WITH([-lcurses -ltermcap])
      CVC4_TRY_STATIC_READLINE_WITH([-lcurses -ltermcap -ltinfo])
      if test -n "$READLINE_LIBS"; then
        AC_MSG_RESULT([yes, it works])
        with_readline=yes
      else
        AC_MSG_RESULT([no])
        if test "$with_readline" != check; then
          AC_MSG_FAILURE([readline installation appears incompatible with static-binary])
        fi
        with_readline=no
      fi
    else
      with_readline=yes
    fi
  fi
  if test "$with_readline" = yes; then
    have_libreadline=1
    AC_MSG_CHECKING([for type of rl_completion_entry_function])
    AC_LANG_PUSH([C++])
    AC_COMPILE_IFELSE([AC_LANG_PROGRAM([
#include <stdio.h>
#include <readline/readline.h>
char* foo(const char*, int) { return (char*)0; }],[
rl_completion_entry_function = foo;])],
      [AC_MSG_RESULT([char* (*)(const char*, int)])
       readline_compentry_func_returns_charp=1],
      [AC_MSG_RESULT([Function])])
    AC_LANG_POP([C++])
  else
    have_libreadline=0
    READLINE_LIBS=
  fi
fi
])# CVC4_CHECK_FOR_READLINE

# CVC4_TRY_READLINE_WITH(LIBS)
# ----------------------------
# Try AC_CHECK_LIB(readline) with the given linking libraries
AC_DEFUN([CVC4_TRY_READLINE_WITH], [
if test -z "$READLINE_LIBS"; then
  unset ac_cv_lib_readline_readline
  AC_CHECK_LIB([readline], [readline],
               [AC_CHECK_HEADER([readline/readline.h],
                  [READLINE_LIBS="-lreadline $1"],
                  [])],
               [], [$1])
fi
])# CVC4_TRY_READLINE_WITH

# CVC4_TRY_STATIC_READLINE_WITH(LIBS)
# -----------------------------------
# Try AC_CHECK_LIB(readline) with the given linking libraries
AC_DEFUN([CVC4_TRY_STATIC_READLINE_WITH], [
if test -z "$READLINE_LIBS"; then
  AC_LANG_PUSH([C++])
  cvc4_save_LIBS="$LIBS"
  cvc4_save_LDFLAGS="$LDFLAGS"
  LDFLAGS="-static $LDFLAGS"
  LIBS="-lreadline $1"
  AC_LINK_IFELSE([AC_LANG_PROGRAM([#include <readline/readline.h>],
                                  [readline("")])],
    [READLINE_LIBS="-lreadline $1"],
    [])
  LIBS="$cvc4_save_LIBS"
  LDFLAGS="$cvc4_save_LDFLAGS"
  AC_LANG_POP([C++])
fi
])# CVC4_TRY_STATIC_READLINE_WITH
