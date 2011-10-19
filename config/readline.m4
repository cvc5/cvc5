# CVC4_CHECK_FOR_READLINE
# -----------------------
# Look for readline and link it in, but allow user to disable.
AC_DEFUN([CVC4_CHECK_FOR_READLINE], [
AC_MSG_CHECKING([whether user requested readline support])
AC_ARG_WITH([readline], [AS_HELP_STRING([--with-readline], [support the readline library])], [], [with_readline=check])
LIBREADLINE=
if test "$with_readline" = no; then
  AC_MSG_RESULT([no, readline disabled by user])
else
  if test "$with_readline" = check; then
    AC_MSG_RESULT([no preference by user, will auto-detect])
  else
    AC_MSG_RESULT([yes, readline enabled by user])
  fi
  AC_CHECK_LIB([readline], [readline],
               [AC_CHECK_HEADER([readline/readline.h],
                  [READLINE_LIBS="-lreadline -lncurses"],
                  [if test "$with_readline" != check; then
                     AC_MSG_FAILURE([cannot find libreadline!])
                   fi])],
               [if test "$with_readline" != check; then
                  AC_MSG_FAILURE([cannot find libreadline!])
                fi], -lncurses)
  if test -z "$READLINE_LIBS"; then
    with_readline=no
  else
    # make sure it works in static builds, too
    if test "$enable_static_binary" = yes; then
      AC_MSG_CHECKING([whether statically-linked readline is functional])
      AC_LANG_PUSH([C++])
      cvc4_save_LIBS="$LIBS"
      cvc4_save_LDFLAGS="$LDFLAGS"
      LDFLAGS="-static $LDFLAGS"
      LIBS="$READLINE_LIBS $LIBS"
      AC_LINK_IFELSE(AC_LANG_PROGRAM([#include <readline/readline.h>],
                                     [readline("")]),
        [ AC_MSG_RESULT([yes, it works])
          with_readline=yes ],
        [ AC_MSG_RESULT([no])
          if test "$with_readline" != check; then
            AC_MSG_FAILURE([readline installation incompatible with static-binary])
          fi
          with_readline=no ])
      LIBS="$cvc4_save_LIBS"
      LDFLAGS="$cvc4_save_LDFLAGS"
      AC_LANG_POP([C++])
    else
      with_readline=yes
    fi
  fi
  if test "$with_readline" = yes; then
    HAVE_LIBREADLINE=1
  else
    HAVE_LIBREADLINE=0
  fi
  AC_DEFINE_UNQUOTED([HAVE_LIBREADLINE], ${HAVE_LIBREADLINE}, [Define to 1 to use libreadline])
  AC_SUBST([READLINE_LIBS])
fi
])# CVC4_CHECK_FOR_READLINE

