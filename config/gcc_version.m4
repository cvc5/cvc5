# GCC version 4.5.1 builds Minisat incorrectly with -O2
# and that gives incorrect answers!  Warn the user!
AC_DEFUN([CVC4_GCC_VERSION], [
  if expr "$($CC -dumpversion)" : '4\.5\.1' &>/dev/null; then
    CVC4_INTEGRITY_WARNING="GCC 4.5.1's optimizer is known to make errors building Minisat (and by extension CVC4)"
  fi
])# CVC4_GCC_VERSION
