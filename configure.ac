#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

dnl Preprocess CL args. Defined in config/cvc4.m4
CVC4_AC_INIT

AC_PREREQ(2.64)
AC_INIT
AC_CONFIG_SRCDIR([src/include/cvc4_config.h])
AC_CONFIG_AUX_DIR([config])
AC_CONFIG_MACRO_DIR([config])

CVC4_RELEASE=prerelease

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

CVC4_LIBRARY_VERSION=0:0:0
CVC4_PARSER_LIBRARY_VERSION=0:0:0

# Using the AC_CANONICAL_* macros destroy the command line you get
# from $@, which we want later for determining the build profile.  So
# we save it.  (We can't do our build profile stuff here, or it's not
# included in the output... autoconf overrides us on the orderings of
# some things.)
config_cmdline="$@"

# turn off static lib building by default
AC_ENABLE_SHARED
AC_DISABLE_STATIC

AC_CANONICAL_BUILD
AC_CANONICAL_HOST
AC_CANONICAL_TARGET

# Features requested by the user
AC_MSG_CHECKING([for requested build profile])
AC_ARG_WITH([build],
  [AS_HELP_STRING([--with-build=profile],
     [for profile in {production,debug,default,competition}])])

if test -z "${with_build+set}" -o "$with_build" = default; then
  with_build=default
fi
if test -z "${enable_optimized+set}" -a -z "${enable_debug_symbols+set}" -a -z "${enable_assertions+set}" -a -z "${enable_tracing+set}" -a -z "${enable_muzzle+set}" -a -z "${enable_coverage+set}" -a -z "${enable_profiling+set}"; then
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
AC_MSG_RESULT([$with_build])

AC_MSG_CHECKING([for appropriate build string])
build_type=`$ac_confdir/config/build-type $with_build $btargs`
if test "$custom_build_profile" = yes; then
  if test "$with_build" = default; then
    build_type=`$ac_confdir/config/build-type custom $btargs`
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
elif test -e src/include/cvc4_config.h; then
  AC_MSG_RESULT([builds/$target/$build_type])
  echo
  if test -z "$ac_srcdir"; then
    mkbuilddir=./config/mkbuilddir
  else
    mkbuilddir=$ac_srcdir/config/mkbuilddir
  fi
  echo $mkbuilddir "$target" "$build_type"
  $mkbuilddir "$target" "$build_type"
  echo cd "builds/$target/$build_type"
  cd "builds/$target/$build_type"
  CVC4_CONFIGURE_IN_BUILDS=yes; export CVC4_CONFIGURE_IN_BUILDS
  echo ../../../configure $config_cmdline
  exec ../../../configure $config_cmdline
else
  AC_MSG_RESULT([this one (user-specified)])
fi

# Unpack standard build types. Any particular options can be overriden with
# --enable/disable-X options
case "$with_build" in
  production) # highly optimized, no assertions, no tracing
    CVC4CPPFLAGS=
    CVC4CXXFLAGS=-O3
    CVC4LDFLAGS=
    if test -z "${enable_assertions+set}"; then enable_assertions=no             ; fi
    if test -z "${enable_tracing+set}"   ; then enable_tracing=no                ; fi
    if test -z "${enable_muzzle+set}"    ; then enable_muzzle=no                 ; fi
    ;;
  debug) # Unoptimized, debug symbols, assertions, tracing
    CVC4CPPFLAGS=-DCVC4_DEBUG
    CVC4CXXFLAGS='-O0 -fno-inline -ggdb3'
    CVC4LDFLAGS=
    if test -z "${enable_assertions+set}"; then enable_assertions=yes            ; fi
    if test -z "${enable_tracing+set}"   ; then enable_tracing=yes               ; fi
    if test -z "${enable_muzzle+set}"    ; then enable_muzzle=no                 ; fi
    ;;
  default) # moderately optimized, assertions, tracing
    CVC4CPPFLAGS=
    CVC4CXXFLAGS=-O2
    CVC4LDFLAGS=
    if test -z "${enable_assertions+set}"; then enable_assertions=yes            ; fi
    if test -z "${enable_tracing+set}"   ; then enable_tracing=yes               ; fi
    if test -z "${enable_muzzle+set}"    ; then enable_muzzle=no                 ; fi
    ;;
  competition) # maximally optimized, no assertions, no tracing, muzzled
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

AC_MSG_CHECKING([whether to optimize libcvc4])

AC_ARG_ENABLE([optimized],
  [AS_HELP_STRING([--enable-optimized],       
     [optimize the build])])

if test -z "${enable_optimized+set}"; then
  enable_optimized=no
fi

AC_MSG_RESULT([$enable_optimized])

if test "$enable_optimized" = yes; then
  CVC4CXXFLAGS="$CVC4CXXFLAGS -O3"
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
  CVC4CXXFLAGS="$CVC4CXXFLAGS -ggdb3"
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
  CVC4CPPFLAGS="$CVC4CPPFLAGS -DCVC4_ASSERTIONS"
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
  CVC4CPPFLAGS="$CVC4CPPFLAGS -DCVC4_TRACING"
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
  CVC4CPPFLAGS="$CVC4CPPFLAGS -DCVC4_MUZZLE"
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
  CVC4CXXFLAGS="$CVC4CXXFLAGS --coverage"
  CVC4LDFLAGS="$CVC4LDFLAGS --coverage"
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
  CVC4CXXFLAGS="$CVC4CXXFLAGS -pg"
  CVC4LDFLAGS="$CVC4LDFLAGS -pg"
fi

AM_INIT_AUTOMAKE(cvc4, $CVC4_RELEASE)
AC_CONFIG_HEADERS([config.h])

# Initialize libtool's configuration options.
_LT_SET_OPTION([LT_INIT],[win32-dll])
LT_INIT

# Checks for programs.
AC_PROG_CC
AC_PROG_CXX
AC_PROG_INSTALL
# Check for ANTLR runantlr script (defined in config/antlr.m4)
AC_PROG_ANTLR

AC_CHECK_PROG(DOXYGEN, doxygen, doxygen, [])

if test -z "$DOXYGEN"; then
  AC_MSG_WARN([documentation targets require doxygen.  Set your PATH appropriately or set DOXYGEN to point to a valid doxygen binary.])
fi

AC_ARG_VAR(DOXYGEN, [location of doxygen binary])

AC_SUBST([CXXTEST])

AC_ARG_WITH([cxxtest-dir], 
  [AS_HELP_STRING([--with-cxxtest-dir=DIR], [path to CxxTest installation])],
  [CXXTEST="$withval"])

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

AM_CONDITIONAL([HAVE_CXXTESTGEN], [test -n "$CXXTESTGEN"])

AC_ARG_VAR(TEST_CPPFLAGS, [CXXFLAGS to use when testing (default=$CPPFLAGS)])
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
AC_CHECK_LIB(gmp, __gmpz_init, , [AC_MSG_ERROR([GNU MP not found, see http://gmplib.org/])])
# Check for antlr C++ runtime (defined in config/antlr.m4)
AC_LIB_ANTLR

# Checks for header files.
AC_CHECK_HEADERS([getopt.h unistd.h])

# Checks for typedefs, structures, and compiler characteristics.
AC_HEADER_STDBOOL
AC_TYPE_UINT16_T
AC_TYPE_UINT32_T
AC_TYPE_UINT64_T
AC_TYPE_SIZE_T

# Checks for library functions.
# (empty)

# Some definitions for config.h
# (empty)

# Prepare configure output

if test "$enable_shared" = yes; then BUILDING_SHARED=1; fi
if test "$enable_static" = yes; then BUILDING_STATIC=1; fi
AC_SUBST(BUILDING_SHARED)
AC_SUBST(BUILDING_STATIC)

AC_SUBST(CVC4_LIBRARY_VERSION)
AC_SUBST(CVC4_PARSER_LIBRARY_VERSION)

CPPFLAGS="${CPPFLAGS:+$CPPFLAGS }$CVC4CPPFLAGS"
CXXFLAGS="${CXXFLAGS:+$CXXFLAGS }$CVC4CXXFLAGS -Wno-deprecated"
LDFLAGS="${LDFLAGS:+$LDFLAGS }$CVC4LDFLAGS"

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

AC_CONFIG_FILES([
  Makefile.builds
  Makefile]
  m4_esyscmd([find contrib/ doc/ src/ test/ -name Makefile.am | sed 's,\.am$,,'])
)

AC_OUTPUT

# Final information to the user

if test "$custom_build_profile" = yes; then
  if test "$with_build" = default; then
    with_build=custom
  else
    AC_MSG_WARN([])
    AC_MSG_WARN([This is a customized $with_build build profile.])
    AC_MSG_WARN([])
    with_build="$with_build-custom"
  fi
fi

support_unit_tests='cxxtest not found; unit tests not supported'
if test -n "$CXXTEST"; then
  support_unit_tests='unit testing infrastructure enabled in build directory'
fi

cat <<EOF

CVC4 $VERSION

Build profile: $with_build
Build ID     : $build_type
Optimized    : $enable_optimized
Debug symbols: $enable_debug_symbols
Assertions   : $enable_assertions
Tracing      : $enable_tracing
Muzzle       : $enable_muzzle
gcov support : $enable_coverage
gprof support: $enable_profiling
unit tests   : $support_unit_tests

CPPFLAGS     : $CPPFLAGS
CXXFLAGS     : $CXXFLAGS
LDFLAGS      : $LDFLAGS

libcvc4 version      : $CVC4_LIBRARY_VERSION
libcvc4parser version: $CVC4_PARSER_LIBRARY_VERSION

Now just type make, followed by make check or make install, as you like.

EOF
