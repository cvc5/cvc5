#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

m4_define(_CVC4_MAJOR,          0 )      dnl version (major)
m4_define(_CVC4_MINOR,          0 )      dnl version (minor)
m4_define(_CVC4_RELEASE,        0 )      dnl version (alpha)
m4_define(_CVC4_RELEASE_STRING, [prerelease]) dnl version string

dnl Preprocess CL args. Defined in config/cvc4.m4
CVC4_AC_INIT

AC_PREREQ(2.61)
AC_INIT([cvc4], _CVC4_RELEASE_STRING)
AC_CONFIG_SRCDIR([src/include/cvc4_public.h])
AC_CONFIG_AUX_DIR([config])
AC_CONFIG_MACRO_DIR([config])
AC_CONFIG_LIBOBJ_DIR([src/lib])

m4_ifdef([AM_SILENT_RULES],[AM_SILENT_RULES([yes])])

CVC4_MAJOR=_CVC4_MAJOR
CVC4_MINOR=_CVC4_MINOR
CVC4_RELEASE=_CVC4_RELEASE
CVC4_RELEASE_STRING=_CVC4_RELEASE_STRING

# Libtool version numbers for libraries
# Version numbers are in the form current:revision:age
#
# current -
#   increment if interfaces have been added, removed or changed
# revision -
#   increment if source code has changed
#   set to zero if current is incremented
# age -
#   increment if interfaces have been added
#   set to zero if interfaces have been removed
#   or changed
#
# For more information, see:
# http://www.gnu.org/software/libtool/manual/libtool.html#Versioning
# For guidance on when to change the version number, refer to the
# developer's guide.

CVC4_LIBRARY_VERSION=$CVC4_MAJOR:$CVC4_MINOR:$CVC4_RELEASE
CVC4_PARSER_LIBRARY_VERSION=$CVC4_MAJOR:$CVC4_MINOR:$CVC4_RELEASE

# Using the AC_CANONICAL_* macros destroy the command line you get
# from $@, which we want later for determining the build profile.  So
# we save it.  (We can't do our build profile stuff here, or it's not
# included in the output... autoconf overrides us on the orderings of
# some things.)
config_cmdline="$@"

# remember if the user set these explicitly (or whether autoconf does)
user_specified_enable_or_disable_static=${enable_static+yes}
user_specified_enable_or_disable_shared=${enable_shared+yes}

if test -e src/include/cvc4_public.h; then
  CVC4_CONFIGURE_AT_TOP_LEVEL=yes
else
  CVC4_CONFIGURE_AT_TOP_LEVEL=no
fi

# override autoconf: we don't want it giving us CFLAGS/CXXFLAGS, but we do
# want to respect the user's flags
if test -z "${CFLAGS+set}"; then CFLAGS=; fi
if test -z "${CXXFLAGS+set}"; then CXXFLAGS=; fi

# on by default
AM_MAINTAINER_MODE([enable])

# turn off static lib building by default
AC_ENABLE_SHARED
AC_DISABLE_STATIC

AC_CANONICAL_BUILD
AC_CANONICAL_HOST
AC_CANONICAL_TARGET

if test "$enable_shared" = no -a "$user_specified_enable_or_disable_shared" = yes; then
  enable_static=yes
fi

# Features requested by the user
AC_MSG_CHECKING([for requested build profile])
AC_ARG_WITH([build],
  [AS_HELP_STRING([--with-build=profile],
     [for profile in {production,debug,default,competition}])])

if test -z "${with_build+set}" -o "$with_build" = default; then
  with_build=default
fi
if test -z "${enable_optimized+set}" -a -z "${enable_debug_symbols+set}" -a -z "${enable_assertions+set}" -a -z "${enable_tracing+set}" -a -z "${enable_muzzle+set}" -a -z "${enable_coverage+set}" -a -z "${enable_profiling+set}" -a -z "${enable_statistics+set}" -a -z "${with_gmp+set}" -a -z "${with_cln+set}"; then
  custom_build_profile=no
else
  custom_build_profile=yes
fi
btargs=
if test -n "${enable_optimized+set}"; then
  if test "$enable_optimized" = yes; then
    btargs="$btargs optimized"
  else
    btargs="$btargs nooptimized"
  fi
fi
if test -n "${enable_static_binary+set}"; then
  if test "$enable_static_binary" = yes; then
    btargs="$btargs staticbinary"
  else
    btargs="$btargs nostaticbinary"
  fi
fi
if test -n "${enable_debug_symbols+set}"; then
  if test "$enable_debug_symbols" = yes; then
    btargs="$btargs debugsymbols"
  else
    btargs="$btargs nodebugsymbols"
  fi
fi
if test -n "${enable_assertions+set}"; then
  if test "$enable_assertions" = yes; then
    btargs="$btargs assertions"
  else
    btargs="$btargs noassertions"
  fi
fi
if test -n "${enable_tracing+set}"; then
  if test "$enable_tracing" = yes; then
    btargs="$btargs tracing"
  else
    btargs="$btargs notracing"
  fi
fi
if test -n "${enable_muzzle+set}"; then
  if test "$enable_muzzle" = yes; then
    btargs="$btargs muzzle"
  else
    btargs="$btargs nomuzzle"
  fi
fi
if test -n "${enable_coverage+set}"; then
  if test "$enable_coverage" = yes; then
    btargs="$btargs coverage"
  else
    btargs="$btargs nocoverage"
  fi
fi
if test -n "${enable_profiling+set}"; then
  if test "$enable_profiling" = yes; then
    btargs="$btargs profiling"
  else
    btargs="$btargs noprofiling"
  fi
fi
if test -n "${enable_statistics+set}"; then
  if test "$enable_statistics" = yes; then
    btargs="$btargs statistics"
  else
    btargs="$btargs nostatistics"
  fi
fi
AC_MSG_RESULT([$with_build])

AM_INIT_AUTOMAKE([1.11 no-define parallel-tests color-tests])
AC_CONFIG_HEADERS([cvc4autoconfig.h])

# Initialize libtool's configuration options.
_LT_SET_OPTION([LT_INIT],[win32-dll])
LT_INIT

# Checks for programs.
AC_PROG_CC
AC_PROG_CXX
AC_PROG_INSTALL

# determine whether to use CLN or GMP.
# we do this here so it can affect the build directory

# [chris 8/24/2010] The user *must* specify --with-cln to get CLN
# (and, thus, opt in to the GPL dependency).

cvc4_use_gmp=0
cvc4_use_cln=0

AC_ARG_WITH(
  [cln],
  AS_HELP_STRING(
    [--with-cln],
    [use CLN instead of GMP]
  ),
  [if test "$withval" != no; then
     cvc4_use_cln=1
   fi
  ]
)

# [chris 8/24/2010] --with-gmp has no practical effect, since GMP is
# the default. Could be useful if other options are added later.

AC_ARG_WITH(
  [gmp],
  AS_HELP_STRING(
    [--with-gmp],
    [use GMP instead of CLN (default)]
  ),
  [if test "$withval" = no; then
     if test $cvc4_use_cln = 0; then
       AC_MSG_ERROR([You must use either CLN and GMP.  Please pick one.])
     fi
   else
     cvc4_use_gmp=1
   fi
  ]
)

if test $cvc4_use_cln = 1 && test $cvc4_use_gmp = 1; then
  # error
  AC_MSG_ERROR([You cannot use both CLN and GMP.  Please pick one.])
fi

if test $cvc4_use_cln = 1; then
  # [mdeters] The PKG_CHECK_MODULES macro isn't customizable and doesn't fail
  # gracefully.  You can only specify it once for a given library name.  That
  # is, even on separate if/else branches, you can't put
  # PKG_CHECK_MODULES([CLN], ...).  That's why things are so convoluted here,
  # we have to have PKG_CHECK_MODULES _exactly_ once in configure.ac !
  PKG_CHECK_MODULES([CLN], [cln >= 1.2.2],
    [cvc4_use_cln=1],
    [if test $cvc4_use_cln = 0; then
       # fall back to GMP
       AC_MSG_NOTICE([CLN not installed (or too old) or pkgconfig missing, will use gmp])
     else
       # fail
       AC_MSG_ERROR([CLN not installed (or too old) or pkgconfig missing])
     fi
    ]
  )
fi
if test $cvc4_use_cln = 0; then
  # try GMP, fail if not found
  AC_CHECK_LIB(gmp, __gmpz_init, , [AC_MSG_ERROR([GNU MP (libgmp) not found, see http://gmplib.org/])])
  AC_CHECK_LIB(gmpxx, __gmpz_init, , [AC_MSG_ERROR([GNU MP C++ library (libgmpxx) not found, see http://gmplib.org/])])
  cvc4_cln_or_gmp=gmp
else
  CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }$CLN_CFLAGS"
  CVC4CXXFLAGS="${CVC4CXXFLAGS:+$CVC4CXXFLAGS }$CLN_CFLAGS"
  CVC4CFLAGS="${CVC4CFLAGS:+$CVC4CFLAGS }$CLN_CFLAGS"
  LIBS="${LIBS:+$LIBS }$CLN_LIBS"
  cvc4_cln_or_gmp=cln
fi

if test $cvc4_cln_or_gmp = cln; then
  AC_DEFINE_UNQUOTED(CVC4_CLN_IMP, [], [Defined if using the CLN multi-precision arithmetic library.])
else
  AC_DEFINE_UNQUOTED(CVC4_GMP_IMP, [], [Defined if using the GMP multi-precision arithmetic library.])
fi
AM_CONDITIONAL([CVC4_CLN_IMP], [test $cvc4_cln_or_gmp = cln])
AM_CONDITIONAL([CVC4_GMP_IMP], [test $cvc4_cln_or_gmp = gmp])

# construct the build string
AC_MSG_CHECKING([for appropriate build string])
if test -z "$ac_confdir"; then
  ac_confdir="$srcdir"
fi
build_type=`$ac_confdir/config/build-type $with_build $btargs $cvc4_cln_or_gmp`
if test "$custom_build_profile" = yes; then
  if test "$with_build" = default; then
    build_type=`$ac_confdir/config/build-type custom $btargs $cvc4_cln_or_gmp`
  fi
fi
AC_MSG_RESULT($build_type)

# Require building in target and build-specific build directory:
#
# If the configure script is invoked from the top-level source
# directory, it creates a suitable build directory (based on the build
# architecture and build profile from $build_type), changes into it,
# and reinvokes itself.  CVC4_CONFIGURE_IN_BUILDS is an envariable
# that breaks any possibility of infinite recursion in this process.
AC_MSG_CHECKING([what dir to configure])
if test "$CVC4_CONFIGURE_IN_BUILDS" = yes; then
  AC_MSG_RESULT([this one (in builds/)])
elif test "$CVC4_CONFIGURE_AT_TOP_LEVEL" = yes; then
  AC_MSG_RESULT([builds/$target/$build_type])
  $as_echo
  if test -z "$ac_srcdir"; then
    mkbuilddir=./config/mkbuilddir
  else
    mkbuilddir=$ac_srcdir/config/mkbuilddir
  fi
  $as_echo "$mkbuilddir $target $build_type"
  source $mkbuilddir "$target" "$build_type"
  $as_echo "cd builds/$target/$build_type"
  cd "builds/$target/$build_type"
  CVC4_CONFIGURE_IN_BUILDS=yes; export CVC4_CONFIGURE_IN_BUILDS
  $as_echo "../../../configure $config_cmdline"
  `pwd`/../../../configure $config_cmdline
  exitval=$?
  cd ../../..
  if test $exitval -eq 0; then
    cat >config.reconfig <<EOF
[#!/bin/bash
# Generated by configure, `date`
# This script is part of CVC4.

cd "\`dirname \\"\$0\\"\`"

if test -d builds; then :; else echo 'No builds/ directory!' >&2; exit; fi

current=(\`grep '^CURRENT_BUILD' builds/current | sed 's,^CURRENT_BUILD *= *\([^/]*\\)/\\(.*\\),\\1 \\2,'\`)
arch=\${current[0]}
build=\${current[1]}

echo "reconfiguring in builds/\$arch/\$build..."
cd "builds/\$arch/\$build"
echo ./config.status "\$@"
./config.status "\$@"]
EOF
    chmod +x config.reconfig
  fi
  exit $exitval
else
  AC_MSG_RESULT([this one (user-specified)])
fi

# Unpack standard build types. Any particular options can be overriden with
# --enable/disable-X options
case "$with_build" in
  production) # highly optimized, no assertions, no tracing
    CVC4CPPFLAGS=
    CVC4CXXFLAGS=
    CVC4CFLAGS=
    CVC4LDFLAGS=
    FLAG_VISIBILITY_HIDDEN='-fvisibility=hidden'
    if test -z "${OPTLEVEL+set}"            ; then OPTLEVEL=3                       ; fi
    if test -z "${enable_optimized+set}"    ; then enable_optimized=yes             ; fi
    if test -z "${enable_debug_symbols+set}"; then enable_debug_symbols=yes         ; fi
    if test -z "${enable_statistics+set}"   ; then enable_statistics=yes            ; fi
    if test -z "${enable_assertions+set}"   ; then enable_assertions=no             ; fi
    if test -z "${enable_tracing+set}"      ; then enable_tracing=no                ; fi
    if test -z "${enable_muzzle+set}"       ; then enable_muzzle=no                 ; fi
    ;;
  debug) # unoptimized, debug symbols, assertions, tracing
    CVC4CPPFLAGS=-DCVC4_DEBUG
    CVC4CXXFLAGS='-fno-inline'
    CVC4CFLAGS='-fno-inline'
    CVC4LDFLAGS=
    FLAG_VISIBILITY_HIDDEN=
    if test -z "${enable_optimized+set}"    ; then enable_optimized=no              ; fi
    if test -z "${enable_debug_symbols+set}"; then enable_debug_symbols=yes         ; fi
    if test -z "${enable_statistics+set}"   ; then enable_statistics=yes            ; fi
    if test -z "${enable_assertions+set}"   ; then enable_assertions=yes            ; fi
    if test -z "${enable_tracing+set}"      ; then enable_tracing=yes               ; fi
    if test -z "${enable_muzzle+set}"       ; then enable_muzzle=no                 ; fi
    ;;
  default) # moderately optimized, assertions, tracing
    CVC4CPPFLAGS=
    CVC4CXXFLAGS=
    CVC4CFLAGS=
    CVC4LDFLAGS=
    FLAG_VISIBILITY_HIDDEN='-fvisibility=hidden'
    if test -z "${OPTLEVEL+set}"            ; then OPTLEVEL=2                       ; fi
    if test -z "${enable_optimized+set}"    ; then enable_optimized=yes             ; fi
    if test -z "${enable_debug_symbols+set}"; then enable_debug_symbols=yes         ; fi
    if test -z "${enable_statistics+set}"   ; then enable_statistics=yes            ; fi
    if test -z "${enable_assertions+set}"   ; then enable_assertions=yes            ; fi
    if test -z "${enable_tracing+set}"      ; then enable_tracing=yes               ; fi
    if test -z "${enable_muzzle+set}"       ; then enable_muzzle=no                 ; fi
    ;;
  competition) # maximally optimized, no assertions, no tracing, muzzled
    CVC4CPPFLAGS='-DCVC4_COMPETITION_MODE'
    CVC4CXXFLAGS='-funroll-all-loops -fexpensive-optimizations -fno-enforce-eh-specs'
    CVC4CFLAGS='-funroll-all-loops -fexpensive-optimizations -fno-enforce-eh-specs'
    CVC4LDFLAGS=
    FLAG_VISIBILITY_HIDDEN='-fvisibility=hidden'
    if test -z "${OPTLEVEL+set}"            ; then OPTLEVEL=9                       ; fi
    if test -z "${enable_optimized+set}"    ; then enable_optimized=yes             ; fi
    if test -z "${enable_debug_symbols+set}"; then enable_debug_symbols=no          ; fi
    if test -z "${enable_statistics+set}"   ; then enable_statistics=no             ; fi
    if test -z "${enable_assertions+set}"   ; then enable_assertions=no             ; fi
    if test -z "${enable_tracing+set}"      ; then enable_tracing=no                ; fi
    if test -z "${enable_muzzle+set}"       ; then enable_muzzle=yes                ; fi
    if test -z "${user_specified_enable_or_disable_shared}"; then enable_shared=no; fi
    if test -z "${user_specified_enable_or_disable_static}"; then enable_static=yes; fi
    if test -z "${enable_static_binary+set}"; then enable_static_binary=yes         ; fi
    ;;
  *)
    AC_MSG_FAILURE([unknown build profile: $with_build])
    ;;
esac
if test -z "${OPTLEVEL+set}"; then OPTLEVEL=3; fi

AM_CONDITIONAL([CVC4_BUILD_PROFILE_PRODUCTION],  [test "$with_build" = production])
AM_CONDITIONAL([CVC4_BUILD_PROFILE_DEBUG],       [test "$with_build" = debug])
AM_CONDITIONAL([CVC4_BUILD_PROFILE_DEFAULT],     [test "$with_build" = default])
AM_CONDITIONAL([CVC4_BUILD_PROFILE_COMPETITION], [test "$with_build" = competition])

# permit a static binary
AC_MSG_CHECKING([whether to build a static binary])
AC_ARG_ENABLE([static-binary],
     [AS_HELP_STRING([--enable-static-binary],
                     [build a fully statically-linked binary [default=no]])])
if test -z "${enable_static_binary+set}"; then
  enable_static_binary=no
fi
AC_MSG_RESULT([$enable_static_binary])
if test "$enable_static_binary" = yes -a "$enable_static" != yes; then
  enable_static=yes
  AC_MSG_WARN([forcing static-library building, --enable-static-binary given])
fi

AC_MSG_CHECKING([whether to optimize libcvc4])

AC_ARG_ENABLE([optimized],
  [AS_HELP_STRING([--enable-optimized],
     [optimize the build])])

if test -z "${enable_optimized+set}"; then
  enable_optimized=no
fi

AC_MSG_RESULT([$enable_optimized])

if test "$enable_optimized" = yes; then
  CVC4CXXFLAGS="${CVC4CXXFLAGS:+$CVC4CXXFLAGS }-O$OPTLEVEL"
  CVC4CFLAGS="${CVC4CFLAGS:+$CVC4CFLAGS }-O$OPTLEVEL"
else
  CVC4CXXFLAGS="${CVC4CXXFLAGS:+$CVC4CXXFLAGS }-O0"
  CVC4CFLAGS="${CVC4CFLAGS:+$CVC4CFLAGS }-O0"
fi

AC_MSG_CHECKING([whether to include debugging symbols in libcvc4])

AC_ARG_ENABLE([debug-symbols],
  [AS_HELP_STRING([--disable-debug-symbols],
     [do not include debug symbols in libcvc4])])

if test -z "${enable_debug_symbols+set}"; then
  enable_debug_symbols=yes
fi

AC_MSG_RESULT([$enable_debug_symbols])

if test "$enable_debug_symbols" = yes; then
  CVC4CXXFLAGS="${CVC4CXXFLAGS:+$CVC4CXXFLAGS }-ggdb3"
  CVC4CFLAGS="${CVC4CFLAGS:+$CVC4CFLAGS }-ggdb3"
fi

AC_MSG_CHECKING([whether to include statistics are turned on in libcvc4])

AC_ARG_ENABLE([statistics],
  [AS_HELP_STRING([--disable-statistics],
     [do not include statistics in libcvc4])])

if test -z "${enable_statistics+set}"; then
  enable_statistics=yes
fi

AC_MSG_RESULT([$enable_statistics])

if test "$enable_statistics" = yes; then
  CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-DCVC4_STATISTICS_ON"
fi

AC_MSG_CHECKING([whether to include assertions in build])

AC_ARG_ENABLE([assertions],
  [AS_HELP_STRING([--disable-assertions],
     [turn off assertions in build])])

if test -z "${enable_assertions+set}"; then
  enable_assertions=yes
fi

AC_MSG_RESULT([$enable_assertions])

if test "$enable_assertions" = yes; then
  CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-DCVC4_ASSERTIONS"
fi

AC_MSG_CHECKING([whether to do a traceable build of CVC4])
AC_ARG_ENABLE([tracing],
  [AS_HELP_STRING([--disable-tracing],
     [remove all tracing code from CVC4])])

if test -z "${enable_tracing+set}"; then
  enable_tracing=yes
fi

AC_MSG_RESULT([$enable_tracing])

if test "$enable_tracing" = yes; then
  CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-DCVC4_TRACING"
fi

AC_MSG_CHECKING([whether to do a muzzled build of CVC4])
AC_ARG_ENABLE([muzzle],
  [AS_HELP_STRING([--enable-muzzle],
     [completely silence CVC4; remove ALL non-result output from build])])

if test -z "${enable_muzzle+set}"; then
  enable_muzzle=no
fi

AC_MSG_RESULT([$enable_muzzle])

if test "$enable_muzzle" = yes; then
  CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-DCVC4_MUZZLE"
fi

AC_MSG_CHECKING([whether to do a gcov-enabled build of CVC4])
AC_ARG_ENABLE([coverage],
  [AS_HELP_STRING([--enable-coverage],
     [build with support for gcov coverage testing])])

if test -z "${enable_coverage+set}"; then
  enable_coverage=no
fi

AC_MSG_RESULT([$enable_coverage])

if test "$enable_coverage" = yes; then
  # For coverage testing, we prefer:
  #     --enable-static --disable-shared --disable-static-binary
  # If the user didn't specify these, we force them here.  If the
  # user specified them in opposite phase, give warnings that they
  # shouldn't do that, or bomb out.
  if test "$user_specified_enable_or_disable_shared" != yes; then
    enable_shared=no
    AC_MSG_WARN([turning off shared library building due to --enable-coverage])
  elif test "$enable_shared" = yes; then
    AC_MSG_WARN([])
    AC_MSG_WARN([It is not recommended to configure with --enable-coverage --enable-shared])
    AC_MSG_WARN([gcov does not support shared libraries, so only your static libraries will be coverage-testable.])
    AC_MSG_WARN([Your cvc4 driver and testing binaries will not be coverage-testable.])
    AC_MSG_WARN([])
  fi
  if test "${enable_static_binary+set}" = set -a "$enable_static_binary" = yes; then
    AC_MSG_WARN([])
    AC_MSG_WARN([It is not recommended to configure with --enable-coverage --enable-static-binary])
    AC_MSG_WARN([Your cvc4 driver and testing binaries will be fully-statically linked and may not be coverage-testable.])
    AC_MSG_WARN([])
  fi
  if test "$user_specified_enable_or_disable_static" != yes; then
    enable_static=yes
    AC_MSG_WARN([turning on static library building due to --enable-coverage])
  elif test "$enable_static" != yes; then
    AC_MSG_ERROR([--enable-coverage and --disable-static are incompatible; gcov only supports static libraries.])
  fi

  CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-DCVC4_COVERAGE"
  CVC4CXXFLAGS="${CVC4CXXFLAGS:+$CVC4CXXFLAGS }--coverage"
  CVC4CFLAGS="${CVC4CFLAGS:+$CVC4CFLAGS }--coverage"
  CVC4LDFLAGS="${CVC4LDFLAGS:+$CVC4LDFLAGS }--coverage"
fi

AC_MSG_CHECKING([whether to do a profiling-enabled build of CVC4])

AC_ARG_ENABLE([profiling],
  [AS_HELP_STRING([--enable-profiling],
     [build with support for gprof profiling])])

if test -z "${enable_profiling+set}"; then
  enable_profiling=no
fi

AC_MSG_RESULT([$enable_profiling])

if test "$enable_profiling" = yes; then
  CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-DCVC4_PROFILING"
  CVC4CXXFLAGS="${CVC4CXXFLAGS:+$CVC4CXXFLAGS }-pg"
  CVC4CFLAGS="${CVC4CFLAGS:+$CVC4CFLAGS }-pg"
  CVC4LDFLAGS="${CVC4LDFLAGS:+$CVC4LDFLAGS }-pg"
fi

# Check for ANTLR runantlr script (defined in config/antlr.m4)
AC_PROG_ANTLR

DX_PDF_FEATURE(OFF)
DX_PS_FEATURE(OFF)
DX_DOT_FEATURE(OFF)
DX_INIT_DOXYGEN($PACKAGE_NAME, config/doxygen.cfg, $srcdir/doc)

AC_ARG_VAR(CXXTEST, [path to CxxTest installation])

AC_SUBST([CXXTEST])

AC_ARG_WITH([cxxtest-dir],
  [AS_HELP_STRING([--with-cxxtest-dir=DIR], [path to CxxTest installation])],
  [CXXTEST="$withval"])

# In the case of "./configure --with-cxxtest-dir=../cxxtest" (or other
# relative path) and having switched the configure directory (see above),
# search with respect to the top source dir, not the build dir
if test "$CVC4_CONFIGURE_IN_BUILDS" = yes -a -n "$CXXTEST"; then
  case "$CXXTEST" in
    /*) ;;
    *)  CXXTEST="$srcdir/$CXXTEST" ;;
  esac
fi

CXXTESTGEN=
AC_PATH_PROG(CXXTESTGEN, cxxtestgen.pl, [], [$CXXTEST:$PATH])
if test -z "$CXXTESTGEN"; then
  AC_MSG_NOTICE([unit tests disabled, cxxtestgen.pl not found.])
elif test -z "$CXXTEST"; then
  CXXTEST=`dirname "$CXXTESTGEN"`
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

AM_CONDITIONAL([HAVE_CXXTESTGEN], [test -n "$CXXTESTGEN"])

AC_ARG_VAR(TEST_CPPFLAGS, [CPPFLAGS to use when testing (default=$CPPFLAGS)])
AC_ARG_VAR(TEST_CXXFLAGS, [CXXFLAGS to use when testing (default=$CXXFLAGS)])
AC_ARG_VAR(TEST_LDFLAGS,  [LDFLAGS to use when testing (default=$LDFLAGS)])

AC_ARG_VAR(PERL, [PERL interpreter (used when testing)])

if test -n "$CXXTEST"; then
  if test -z "$PERL"; then
    AC_CHECK_PROGS(PERL, perl, perl, [])
  else
    AC_CHECK_PROG(PERL, "$PERL", "$PERL", [])
  fi

  if test -z "$PERL"; then
    AC_MSG_WARN([unit tests disabled, perl not found.])
    CXXTESTGEN=
    CXXTEST=
  fi
fi

# Checks for libraries.
AC_CHECK_LIB(z, gzread, , [AC_MSG_ERROR([zlib required, install your distro's zlib-dev package or see www.zlib.net])])
AC_CHECK_HEADER(zlib.h, , [AC_MSG_ERROR([zlib required, install your distro's zlib-dev package or see www.zlib.net])])

AC_SEARCH_LIBS([clock_gettime], [rt],
               [AC_DEFINE([HAVE_CLOCK_GETTIME], [1],
                          [Defined to 1 if clock_gettime() is supported by the platform.])],
               [AC_LIBOBJ([clock_gettime])])

# Check for antlr C++ runtime (defined in config/antlr.m4)
AC_LIB_ANTLR

# Checks for header files.
AC_CHECK_HEADERS([getopt.h unistd.h])

# Checks for typedefs, structures, and compiler characteristics.
#AC_HEADER_STDBOOL
# these are bad macros, they clash with system header <stdint.h> !!
#AC_TYPE_UINT16_T
#AC_TYPE_UINT32_T
#AC_TYPE_UINT64_T
#AC_TYPE_SIZE_T

# Check for availability of TLS support (e.g. __thread storage class)
AC_MSG_CHECKING([whether to use compiler-supported TLS if available])
AC_ARG_ENABLE([tls], AS_HELP_STRING([--disable-tls], [don't use compiler-native TLS]))
if test -z "${enable_tls+set}" || test "$enable_tls" = "yes"; then
  AC_MSG_RESULT([yes])
  AX_TLS([CVC4_TLS=$ac_cv_tls], [CVC4_TLS=])
else
  AC_MSG_RESULT([no])
  CVC4_TLS=
fi
if test -n "$CVC4_TLS"; then
  CVC4_TLS_SUPPORTED=1
else
  CVC4_TLS='pthread_getspecific()'
  CVC4_TLS_SUPPORTED=0
fi
AC_SUBST([CVC4_TLS])
AC_SUBST([CVC4_TLS_SUPPORTED])

# Checks for library functions.
# (empty)

# Some definitions for config.h
# (empty)

# Prepare configure output

if test "$enable_shared" = yes; then BUILDING_SHARED=1; else BUILDING_SHARED=0; fi
if test "$enable_static" = yes; then BUILDING_STATIC=1; else BUILDING_STATIC=0; fi
if test "$enable_static_binary" = yes; then STATIC_BINARY=1; else STATIC_BINARY=0; fi
AC_SUBST(BUILDING_SHARED)
AC_SUBST(BUILDING_STATIC)
AC_SUBST(STATIC_BINARY)
AM_CONDITIONAL([STATIC_BINARY], [test "$enable_static_binary" = yes])
AM_CONDITIONAL([COVERAGE_ENABLED], [test "$enable_coverage" = yes])

AC_SUBST(CVC4_LIBRARY_VERSION)
AC_SUBST(CVC4_PARSER_LIBRARY_VERSION)

AC_DEFINE_UNQUOTED(CVC4_MAJOR, ${CVC4_MAJOR}, [Major component of the version of CVC4.])
AC_DEFINE_UNQUOTED(CVC4_MINOR, ${CVC4_MINOR}, [Minor component of the version of CVC4.])
AC_DEFINE_UNQUOTED(CVC4_RELEASE, ${CVC4_RELEASE}, [Release component of the version of CVC4.])
AC_DEFINE_UNQUOTED(CVC4_RELEASE_STRING, ["${CVC4_RELEASE_STRING}"], [Full release string for CVC4.])

CPPFLAGS="${CPPFLAGS:+$CPPFLAGS }$CVC4CPPFLAGS"
CXXFLAGS="${CXXFLAGS:+$CXXFLAGS }$CVC4CXXFLAGS -Wno-deprecated"
CFLAGS="${CFLAGS:+$CFLAGS }$CVC4CFLAGS -Wno-deprecated -fexceptions"
LDFLAGS="${LDFLAGS:+$LDFLAGS }$CVC4LDFLAGS"

AC_SUBST(FLAG_VISIBILITY_HIDDEN)

# mk_include
#
# When automake scans Makefiles, it complains about non-standard make
# features (including GNU extensions), and breaks GNU Make's
# "if/endif" construct, replacing the "if" with AM_CONDITIONAL if
# constructs.  automake even follows "include" and messes with
# included Makefiles.
#
# CVC4 assumes GNU Make and we want to use GNU Make if/endifs, so we
# have to hide some included Makefiles with GNU extensions.  We do
# this by defining mk_include as an autoconf substitution and then
# using "@mk_include@ other_makefile" in Makefile.am to include
# makefiles with GNU extensions; this hides them from automake.
mk_include=include
AC_SUBST(mk_include)

# CVC4_FALSE
#
# This is used to _always_ comment out rules in automake makefiles, but
# still trigger certain automake behavior; see test/unit/Makefile.am.
AM_CONDITIONAL([CVC4_FALSE], [false])

# set up substitutions for src/util/{rational,integer}.h.in
if test $cvc4_cln_or_gmp = cln; then
  CVC4_USE_CLN_IMP=1
  CVC4_USE_GMP_IMP=0
else
  CVC4_USE_CLN_IMP=0
  CVC4_USE_GMP_IMP=1
fi
AC_SUBST(CVC4_USE_CLN_IMP)
AC_SUBST(CVC4_USE_GMP_IMP)

AC_CONFIG_FILES([
  Makefile.builds
  Makefile]
  m4_esyscmd([find contrib lib src test -name Makefile.am | sort | sed 's,\.am$,,'])
  src/util/rational.h
  src/util/integer.h
  src/util/tls.h
)

AC_OUTPUT

# Final information to the user
licensewarn=

if test "$custom_build_profile" = yes; then
  if test "$with_build" = default; then
    with_build=custom
  else
    with_build="$with_build (customized)"
  fi
fi

support_unit_tests='cxxtest not found; unit tests not supported'
if test -n "$CXXTEST"; then
  support_unit_tests='unit testing infrastructure enabled in build directory'
fi

if test "$enable_optimized" = yes; then
  optimized="yes, at level $OPTLEVEL"
else
  optimized="no"
fi

if test $cvc4_cln_or_gmp = cln; then
  mplibrary='cln (GPL)'
  licensewarn="${licensewarn}Please note that CVC4 will be built against the Class Library for
Numbers (CLN).  This library is covered under the GPL, so use of this
build of CVC4 will be more restrictive than CVC4's license would
normally suggest.  For full details of CLN and its license, please visit
  http://www.ginac.de/CLN/
To build CVC4 with GMP instead (which is covered under the more permissive
LGPL), configure --without-cln.

"
else
  mplibrary='gmp (LGPL)'
fi

cat <<EOF

CVC4 $VERSION

Build profile: $with_build
Build ID     : $build_type
Optimized    : $optimized
Debug symbols: $enable_debug_symbols
Statistics   : $enable_statistics
Assertions   : $enable_assertions
Tracing      : $enable_tracing
Muzzle       : $enable_muzzle
gcov support : $enable_coverage
gprof support: $enable_profiling
Unit tests   : $support_unit_tests

Static libs  : $enable_static
Shared libs  : $enable_shared
Static binary: $enable_static_binary
TLS support  : $CVC4_TLS

MP library   : $mplibrary

CPPFLAGS     : $CPPFLAGS
CXXFLAGS     : $CXXFLAGS
CFLAGS       : $CFLAGS
LDFLAGS      : $LDFLAGS

libcvc4 version      : $CVC4_LIBRARY_VERSION
libcvc4parser version: $CVC4_PARSER_LIBRARY_VERSION

${licensewarn}Now just type make, followed by make check or make install, as you like.

EOF
