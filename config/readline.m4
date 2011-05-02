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
                  AC_SUBST([READLINE_LDFLAGS], ["-lreadline -lncurses"])
                  AC_DEFINE([HAVE_LIBREADLINE], [1], [Define to 1 to use libreadline]))],
               [if test "$with_readline" != check; then
                  AC_MSG_FAILURE([cannot find libreadline!])
                fi], -lncurses)
  if test -z "$READLINE_LDFLAGS"; then with_readline=no; else with_readline=yes; fi
fi
])# CVC4_CHECK_FOR_READLINE

