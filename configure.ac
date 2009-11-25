#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.63])
AC_INIT([src/include/cvc4.h])
AC_CONFIG_AUX_DIR([config])
#AC_CONFIG_LIBOBJ_DIR([lib])
AC_CONFIG_MACRO_DIR([config])
AM_INIT_AUTOMAKE(cvc4, prerelease)
AC_CONFIG_HEADERS([config.h])

# keep track of whether the user set these (check here, because
# autoconf might set a default later)
AC_MSG_CHECKING([for user CPPFLAGS])
if test -z "${CPPFLAGS+set}"; then user_cppflags=no; else user_cppflags=yes; fi
AC_MSG_RESULT([${CPPFLAGS-none}])
AC_MSG_CHECKING([for user CXXFLAGS])
if test -z "${CXXFLAGS+set}"; then user_cxxflags=no; else user_cxxflags=yes; fi
AC_MSG_RESULT([${CXXFLAGS-none}])
AC_MSG_CHECKING([for user LDFLAGS])
if test -z "${LDFLAGS+set}" ; then user_ldflags=no ; else user_ldflags=yes ; fi
AC_MSG_RESULT([${LDFLAGS-none}])

LT_INIT

AC_LIBTOOL_WIN32_DLL

# Features requested by the user
AC_MSG_CHECKING([for requested build profile])
AC_ARG_WITH([build],             [AS_HELP_STRING([--with-build=profile],     [for profile in {production,debug,default,competition}])])
if test -z "${with_build+set}" -o "$with_build" = default; then
  with_build=default
fi
if test "$user_cppflags" = no -a "$user_cxxflags" = no -a "$user_ldflags" = no -a -z "${enable_optimized+set}" -a -z "${enable_debug_symbols+set}" -a -z "${enable_assertions+set}" -a -z "${enable_tracing+set}" -a -z "${enable_muzzle+set}" -a -z "${enable_coverage+set}" -a -z "${enable_profiling+set}"; then
  non_standard_build_profile=no
else
  non_standard_build_profile=yes
fi
case "$with_build" in
  production)
    CVC4CPPFLAGS=
    CVC4CXXFLAGS=-O3
    CVC4LDFLAGS=
    if test -z "${enable_assertions+set}"; then enable_assertions=no             ; fi
    if test -z "${enable_tracing+set}"   ; then enable_tracing=no                ; fi
    if test -z "${enable_muzzle+set}"    ; then enable_muzzle=no                 ; fi
    ;;
  debug)
    CVC4CPPFLAGS=-DCVC4_DEBUG
    CVC4CXXFLAGS='-O0 -fno-inline -ggdb3'
    CVC4LDFLAGS=
    if test -z "${enable_assertions+set}"; then enable_assertions=yes            ; fi
    if test -z "${enable_tracing+set}"   ; then enable_tracing=yes               ; fi
    if test -z "${enable_muzzle+set}"    ; then enable_muzzle=no                 ; fi
    ;;
  default)
    CVC4CPPFLAGS=
    CVC4CXXFLAGS=-O2
    CVC4LDFLAGS=
    if test -z "${enable_assertions+set}"; then enable_assertions=yes            ; fi
    if test -z "${enable_tracing+set}"   ; then enable_tracing=yes               ; fi
    if test -z "${enable_muzzle+set}"    ; then enable_muzzle=no                 ; fi
    ;;
  competition)
    CVC4CPPFLAGS=
    CVC4CXXFLAGS='-O9 -funroll-all-loops -fexpensive-optimizations -fno-enforce-eh-specs'
    CVC4LDFLAGS=
    if test -z "${enable_assertions+set}"; then enable_assertions=no             ; fi
    if test -z "${enable_tracing+set}"   ; then enable_tracing=no                ; fi
    if test -z "${enable_muzzle+set}"    ; then enable_muzzle=yes                ; fi
    ;;
  *)
    AC_MSG_FAILURE([unknown build profile: $with_build])
    ;;
esac
AC_MSG_RESULT([$with_build])

AC_MSG_CHECKING([whether to optimize libcvc4])
AC_ARG_ENABLE([optimized],       [AS_HELP_STRING([--enable-optimized],       [optimize the build])])
if test -z "${enable_optimized+set}"; then
  enable_optimized=no
fi
AC_MSG_RESULT([$enable_optimized])
if test "$enable_optimized" = yes; then
  CVC4CXXFLAGS="$CVC4CXXFLAGS -O3"
fi

AC_MSG_CHECKING([whether to include debugging symbols in libcvc4])
AC_ARG_ENABLE([debug-symbols],   [AS_HELP_STRING([--disable-debug-symbols],  [do not include debug symbols in libcvc4])])
if test -z "${enable_debug_symbols+set}"; then
  enable_debug_symbols=yes
fi
AC_MSG_RESULT([$enable_debug_symbols])
if test "$enable_debug_symbols" = yes; then
  CVC4CXXFLAGS="$CVC4CXXFLAGS -ggdb3"
fi

AC_MSG_CHECKING([whether to include assertions in build])
AC_ARG_ENABLE([assertions],      [AS_HELP_STRING([--disable-assertions],     [turn off assertions in build])])
if test -z "${enable_assertions+set}"; then
  enable_assertions=yes
fi
AC_MSG_RESULT([$enable_assertions])
if test "$enable_assertions" = yes; then
  CVC4CPPFLAGS="$CVC4CPPFLAGS -DCVC4_ASSERTIONS"
fi

AC_MSG_CHECKING([whether to do a traceable build of CVC4])
AC_ARG_ENABLE([tracing],         [AS_HELP_STRING([--disable-tracing],        [remove all tracing code from CVC4])])
if test -z "${enable_tracing+set}"; then
  enable_tracing=yes
fi
AC_MSG_RESULT([$enable_tracing])
if test "$enable_tracing" = yes; then
  CVC4CPPFLAGS="$CVC4CPPFLAGS -DCVC4_TRACING"
fi

AC_MSG_CHECKING([whether to do a muzzled build of CVC4])
AC_ARG_ENABLE([muzzle],          [AS_HELP_STRING([--enable-muzzle],          [completely silence CVC4; remove ALL non-result output from build])])
if test -z "${enable_muzzle+set}"; then
  enable_muzzle=no
fi
AC_MSG_RESULT([$enable_muzzle])
if test "$enable_muzzle" = yes; then
  CVC4CPPFLAGS="$CVC4CPPFLAGS -DCVC4_MUZZLE"
fi

AC_MSG_CHECKING([whether to do a gcov-enabled build of CVC4])
AC_ARG_ENABLE([coverage],        [AS_HELP_STRING([--enable-coverage],        [build with support for gcov coverage testing])])
if test -z "${enable_coverage+set}"; then
  enable_coverage=no
fi
AC_MSG_RESULT([$enable_coverage])
if test "$enable_coverage" = yes; then
  CVC4CXXFLAGS="$CVC4CXXFLAGS --coverage"
  CVC4LDFLAGS="$CVC4LDFLAGS --coverage"
fi

AC_MSG_CHECKING([whether to do a profiling-enabled build of CVC4])
AC_ARG_ENABLE([profiling],       [AS_HELP_STRING([--enable-profiling],       [build with support for gprof profiling])])
if test -z "${enable_profiling+set}"; then
  enable_profiling=no
fi
AC_MSG_RESULT([$enable_profiling])
if test "$enable_profiling" = yes; then
  CVC4CXXFLAGS="$CVC4CXXFLAGS -pg"
  CVC4LDFLAGS="$CVC4LDFLAGS -pg"
fi




# Checks for programs.
AC_PROG_CC
AC_PROG_CXX
AC_PROG_INSTALL
AC_PROG_LIBTOOL
AM_PROG_LEX
AC_PROG_YACC

AC_CHECK_PROG(DOXYGEN, doxygen, doxygen, [])
if test -z "$DOXYGEN"; then
  AC_MSG_WARN([documentation targets require doxygen.  Set your PATH appropriately or set DOXYGEN to point to a valid doxygen binary.])
fi
AC_ARG_VAR(DOXYGEN, [location of doxygen binary])

CXXTESTGEN=
AC_PATH_PROG(CXXTESTGEN, cxxtestgen.pl, [], [$CXXTEST:$PATH])
if test -z "$CXXTESTGEN"; then
  AC_MSG_NOTICE([unit tests disabled, cxxtestgen.pl not found.])
elif test -z "$CXXTEST"; then
  CXXTEST=$(dirname "$CXXTESTGEN")
  AC_MSG_CHECKING([for location of CxxTest headers])
  if test -e "$CXXTEST/cxxtest/TestRunner.h"; then
    AC_MSG_RESULT([$CXXTEST])
  else
    AC_MSG_RESULT([not found])
    AC_MSG_WARN([unit tests disabled, CxxTest headers not found.])
    CXXTESTGEN=
    CXXTEST=
  fi
fi
AC_ARG_VAR(CXXTEST, [path to CxxTest installation])
AM_CONDITIONAL([HAVE_CXXTESTGEN], [test -n "$CXXTESTGEN"])

AC_ARG_VAR(TEST_CPPFLAGS, [CXXFLAGS to use when testing (default=$CPPFLAGS)])
AC_ARG_VAR(TEST_CXXFLAGS, [CXXFLAGS to use when testing (default=$CXXFLAGS)])
AC_ARG_VAR(TEST_LDFLAGS,  [LDFLAGS to use when testing (default=$LDFLAGS)])

if test -n "$CXXTEST"; then
  AC_CHECK_PROG(PERL, perl, perl, [])
  if test -z "$PERL"; then
    AC_MSG_WARN([unit tests disabled, perl not found.])
    CXXTESTGEN=
    CXXTEST=
  fi
fi

# Checks for libraries.
AC_CHECK_LIB(gmp, __gmpz_init, , [AC_MSG_ERROR([GNU MP not found, see http://gmplib.org/])])

# Checks for header files.
AC_CHECK_HEADERS([getopt.h unistd.h])

# Checks for typedefs, structures, and compiler characteristics.
AC_HEADER_STDBOOL
AC_TYPE_UINT16_T
AC_TYPE_UINT32_T
AC_TYPE_UINT64_T
AC_TYPE_SIZE_T

# Checks for library functions.

# Some definitions for config.h

# Prepare configure output

if test "$user_cppflags" = no; then
  CPPFLAGS="$CVC4CPPFLAGS"
fi
if test "$user_cxxflags" = no; then
  CXXFLAGS="$CVC4CXXFLAGS"
fi
if test "$user_ldflags" = no; then
  LDFLAGS="$CVC4LDFLAGS"
fi

AC_CONFIG_FILES([
  Makefile
  contrib/Makefile
  doc/Makefile
  src/Makefile
  src/expr/Makefile
  src/smt/Makefile
  src/main/Makefile
  src/prop/minisat/Makefile
  src/prop/Makefile
  src/util/Makefile
  src/context/Makefile
  src/parser/Makefile
  src/theory/Makefile
  test/Makefile
  test/regress/Makefile
  test/unit/Makefile
])

AC_OUTPUT

# Final information to the user

cat <<EOF

CVC4 $VERSION

Build profile: $with_build$non_standard
Optimized    : $enable_optimized
Debug symbols: $enable_debug_symbols
Assertions   : $enable_assertions
Tracing      : $enable_tracing
Muzzle       : $enable_muzzle
gcov support : $enable_coverage
gprof support: $enable_profiling

CPPFLAGS     : $CPPFLAGS
CXXFLAGS     : $CXXFLAGS
LDFLAGS      : $LDFLAGS

Now just type make, followed by make check or make install, as you like.

You can use 'make <build_profile>' to reconfig/build a different profile.
Build profiles: production optimized default competition

EOF

if test "$user_cppflags" = yes; then
  AC_MSG_WARN([])
  AC_MSG_WARN([I won't override your CPPFLAGS setting.  But some of your build options to configure may not be honored.])
  AC_MSG_WARN([To support your options to configure, I would like to set CPPFLAGS to:])
  AC_MSG_WARN([    $CVC4CPPFLAGS])
  AC_MSG_WARN([])
fi
if test "$user_cxxflags" = yes; then
  AC_MSG_WARN([])
  AC_MSG_WARN([I won't override your CXXFLAGS setting.  But some of your build options to configure may not be honored.])
  AC_MSG_WARN([To support your options to configure, I would like to set CXXFLAGS to:])
  AC_MSG_WARN([    $CVC4CXXFLAGS])
  AC_MSG_WARN([])
fi
if test "$user_ldflags" = yes; then
  AC_MSG_WARN([])
  AC_MSG_WARN([I won't override your LDFLAGS setting.  But some of your build options to configure may not be honored.])
  AC_MSG_WARN([To support your options to configure, I would like to set LDFLAGS to:])
  AC_MSG_WARN([    $CVC4LDFLAGS])
  AC_MSG_WARN([])
fi

non_standard=
if test "$non_standard_build_profile" = yes; then
  if test "$with_build" = default; then
    with_build=custom
  else
    AC_MSG_WARN([])
    AC_MSG_WARN([This is a non-standard $with_build build profile.])
    AC_MSG_WARN([])
    non_standard=-custom
  fi
fi
