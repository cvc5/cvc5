#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

m4_define(_CVC4_MAJOR,          1)       dnl version (major)
m4_define(_CVC4_MINOR,          5)       dnl version (minor)
m4_define(_CVC4_RELEASE,        0)       dnl version (alpha)
m4_define(_CVC4_EXTRAVERSION,   [-prerelease])      dnl version (extra)
m4_define(_CVC4_RELEASE_STRING, _CVC4_MAJOR[.]_CVC4_MINOR[]m4_if(_CVC4_RELEASE,[0],,[.]_CVC4_RELEASE)_CVC4_EXTRAVERSION) dnl version string

dnl Preprocess CL args. Defined in config/cvc4.m4
CVC4_AC_INIT

AC_PREREQ([2.61])
AC_INIT([cvc4], _CVC4_RELEASE_STRING, [cvc-bugs@cs.nyu.edu])
AC_CONFIG_SRCDIR([src/include/cvc4_public.h])
AC_CONFIG_AUX_DIR([config])
AC_CONFIG_MACRO_DIR([config])
AC_CONFIG_LIBOBJ_DIR([src/lib])
AC_CONFIG_SUBDIRS([proofs/lfsc_checker])

m4_ifdef([AM_SILENT_RULES],[AM_SILENT_RULES([yes])])

CVC4_MAJOR=_CVC4_MAJOR
CVC4_MINOR=_CVC4_MINOR
CVC4_RELEASE=_CVC4_RELEASE
CVC4_EXTRAVERSION=_CVC4_EXTRAVERSION
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

m4_define([library_version], [m4_esyscmd([grep -F "$(grep -v '^#' library_versions | awk '{print$][1}' | sed 's,\\,\\\\\\,g' | (while read r; do if echo "]_CVC4_RELEASE_STRING[" | grep -q "^$r\$"; then echo "$r"; exit; fi; done; echo NO_MATCH_FOUND)) " library_versions | awk 'BEGIN {FS=":";OFS=":";RS=" "} /^$1:/ {print$][2,$][3,$][4}' | head -1])])

m4_define(_CVC4_LIBRARY_VERSION, library_version([libcvc4]))dnl
m4_define(_CVC4_PARSER_LIBRARY_VERSION, library_version([libcvc4parser]))dnl
m4_define(_CVC4_COMPAT_LIBRARY_VERSION, library_version([libcvc4compat]))dnl
m4_define(_CVC4_BINDINGS_LIBRARY_VERSION, library_version([libcvc4bindings]))dnl

m4_define([fatal_error], [m4_errprint(__program__:__file__:__line__[: fatal error: $*
])m4_exit(1)])dnl

m4_ifblank(_CVC4_LIBRARY_VERSION,[fatal_error([no CVC4_LIBRARY_VERSION defined for release version "]_CVC4_RELEASE_STRING[" in library_versions file])])dnl
m4_ifblank(_CVC4_PARSER_LIBRARY_VERSION,[fatal_error([no CVC4_PARSER_LIBRARY_VERSION defined for release version "]_CVC4_RELEASE_STRING[" in library_versions file])])dnl
m4_ifblank(_CVC4_COMPAT_LIBRARY_VERSION,[fatal_error([no CVC4_COMPAT_LIBRARY_VERSION defined for release version "]_CVC4_RELEASE_STRING[" in library_versions file])])dnl
m4_ifblank(_CVC4_BINDINGS_LIBRARY_VERSION,[fatal_error([no CVC4_BINDINGS_LIBRARY_VERSION defined for release version "]_CVC4_RELEASE_STRING[" in library_versions file])])dnl

CVC4_LIBRARY_VERSION=_CVC4_LIBRARY_VERSION
CVC4_PARSER_LIBRARY_VERSION=_CVC4_PARSER_LIBRARY_VERSION
CVC4_COMPAT_LIBRARY_VERSION=_CVC4_COMPAT_LIBRARY_VERSION
CVC4_BINDINGS_LIBRARY_VERSION=_CVC4_BINDINGS_LIBRARY_VERSION

# Using the AC_CANONICAL_* macros destroy the command line you get
# from $@, which we want later for determining the build profile.  So
# we save it.  (We can't do our build profile stuff here, or it's not
# included in the output... autoconf overrides us on the orderings of
# some things.)
config_cmdline=("$@")
cvc4_config_cmdline="${config_cmdline[[@]]}"

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

as_me=configure

if test "$enable_shared" = no -a "$user_specified_enable_or_disable_shared" = yes; then
  enable_static=yes
fi

# Features requested by the user
AC_MSG_CHECKING([for requested build profile])
AC_ARG_WITH([build],
  [AS_HELP_STRING([--with-build=profile],
     [for profile in {production,debug,competition,personal}])])

if test -z "${with_build+set}"; then
  with_build=production
fi
if test -z "${enable_optimized+set}" -a -z "${enable_debug_symbols+set}" -a -z "${enable_assertions+set}" -a -z "${enable_tracing+set}" -a -z "${enable_dumping+set}" -a -z "${enable_muzzle+set}" -a -z "${enable_coverage+set}" -a -z "${enable_profiling+set}" -a -z "${enable_statistics+set}" -a -z "${enable_replay+set}" -a -z "${with_gmp+set}" -a -z "${with_cln+set}" -a -z "${with_glpk+set}" -a -z "${with_abc+set}" -a -z "${with_cryptominisat+set}"; then
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
# --enable-staticbinary is an alias for --enable-static-binary
if test -n "${enable_staticbinary+set}"; then
  enable_static_binary="$enable_staticbinary"
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
if test -n "${enable_proof+set}"; then
  if test "$enable_proof" = yes; then
    btargs="$btargs proof"
  else
    btargs="$btargs noproof"
  fi
fi
if test -n "${enable_tracing+set}"; then
  if test "$enable_tracing" = yes; then
    btargs="$btargs tracing"
  else
    btargs="$btargs notracing"
  fi
fi
if test -n "${enable_dumping+set}"; then
  if test "$enable_dumping" = yes; then
    btargs="$btargs dumping"
  else
    btargs="$btargs nodumping"
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
if test -n "${enable_replay+set}"; then
  if test "$enable_replay" = yes; then
    btargs="$btargs replay"
  else
    btargs="$btargs noreplay"
  fi
fi
if test -n "${with_glpk+set}"; then
  if test "$with_glpk" = yes; then
    btargs="$btargs glpk"
  fi
fi
if test -n "${with_abc+set}"; then
  if test "$with_abc" = yes; then
    btargs="$btargs abc"
  fi
fi
if test -n "${with_cryptominisat+set}"; then
  if test "$with_cryptominisat" = yes; then
    btargs="$btargs cryptominisat"
  fi
fi

AC_MSG_RESULT([$with_build])

AM_INIT_AUTOMAKE([1.11 no-define tar-pax parallel-tests color-tests subdir-objects])
AC_CONFIG_HEADERS([cvc4autoconfig.h])

# automake 1.12 changes the test driver mechanism in a way that is
# completely incompatible with 1.11.  We figure out here which version
# we're using in order to set up test makefiles correctly.
# See http://lists.gnu.org/archive/html/automake/2012-04/msg00060.html
if test -z "$am__api_version"; then
  AC_MSG_ERROR([Cannot determine automake API version ?!])
fi
case "$am__api_version" in
  1.11*) automake111=true ;;
  *) automake111=false ;;
esac
AM_CONDITIONAL([AUTOMAKE_1_11], [$automake111])

# Initialize libtool's configuration options.
# we're not DLL-clean yet (i.e., don't properly use dllexport and dllimport)
# _LT_SET_OPTION([LT_INIT],[win32-dll])
LT_INIT

# Checks for programs.
AC_PROG_CC
AC_PROG_CXX
AC_PROG_INSTALL

CVC4_GCC_VERSION

cvc4_use_gmp=2
cvc4_use_cln=2

AC_ARG_WITH(
  [cln],
  AS_HELP_STRING(
    [--with-cln],
    [use CLN instead of GMP]
  ),
  [case "$withval" in
   y|ye|yes|Y|YE|YES) cvc4_use_cln=1 ;;
   n|no|N|NO) cvc4_use_cln=0 ;;
   esac
  ]
)

AC_ARG_WITH(
  [gmp],
  AS_HELP_STRING(
    [--with-gmp],
    [use GMP instead of CLN]
  ),
  [case "$withval" in
   y|ye|yes|Y|YE|YES) cvc4_use_gmp=1 ;;
   n|no|N|NO) cvc4_use_gmp=0 ;;
   esac
  ]
)

if test $cvc4_use_cln = 1 -a $cvc4_use_gmp = 1 || test $cvc4_use_cln = 0 -a $cvc4_use_gmp = 0; then
  AC_MSG_ERROR([You must use either CLN and GMP.  Please pick one.])
fi
if test $cvc4_use_gmp = 1; then
  cvc4_use_cln=0
elif test $cvc4_use_gmp = 0; then
  cvc4_use_cln=1
elif test $cvc4_use_cln = 1; then
  cvc4_use_gmp=0
elif test $cvc4_use_cln = 0; then
  cvc4_use_gmp=1
fi

# try GMP, fail if not found; GMP is required for both CLN and for GMP
# versions of CVC4
AC_CHECK_LIB(gmp, __gmpz_init, , [AC_MSG_ERROR([GNU MP (libgmp) not found, see http://gmplib.org/])])

if test $cvc4_use_cln = 2; then
  if test "$CVC4_BSD_LICENSED_CODE_ONLY" = 1 -o "$with_portfolio" = yes; then
    cvc4_use_cln=0
    cvc4_use_gmp=1
  fi
fi

if test $cvc4_use_cln != 0; then
  # [mdeters] The PKG_CHECK_MODULES macro isn't customizable and doesn't fail
  # gracefully.  You can only specify it once for a given library name.  That
  # is, even on separate if/else branches, you can't put
  # PKG_CHECK_MODULES([CLN], ...).  That's why things are so convoluted here,
  # we have to have PKG_CHECK_MODULES _exactly_ once in configure.ac !
  PKG_CHECK_MODULES([CLN], [cln >= 1.2.2],
    [AC_LANG_PUSH([C++])
     save_LIBS="$LIBS"
     save_CXXFLAGS="$CXXFLAGS"
     LIBS="$CLN_LIBS $LIBS"
     CXXFLAGS="$CLN_CFLAGS $CXXFLAGS"
     AC_LINK_IFELSE([AC_LANG_PROGRAM([[#include <cln/cln.h>]], [[cln::cl_F pi = "3.1415926";]])], [
       cvc4_use_cln=1
     ], [
       if test $cvc4_use_cln = 1; then
         # fail
         AC_MSG_ERROR([CLN installation missing, too old, or not functional for this architecture])
       else
         # fall back to GMP
         AC_MSG_NOTICE([CLN installation missing, too old, or not functional for this architecture, will use gmp instead])
         cvc4_use_cln=0
         cvc4_use_gmp=1
       fi
     ])
     CXXFLAGS="$save_CXXFLAGS"
     LIBS="$save_LIBS"
     AC_LANG_POP([C++])
    ],
    [if test $cvc4_use_cln = 1; then
       # fail
       AC_MSG_ERROR([CLN not installed (or too old) or pkgconfig missing])
     else
       # fall back to GMP
       AC_MSG_NOTICE([CLN not installed (or too old) or pkgconfig missing, will use gmp])
       cvc4_use_cln=0
       cvc4_use_gmp=1
     fi
    ]
  )
fi
if test $cvc4_use_cln = 0; then
  # try GMPXX, fail if not found; don't need to link against it, only need its header
  AC_LANG_PUSH([C++])
  AC_CHECK_HEADER([gmpxx.h], , [AC_MSG_ERROR([GNU MP C++ library header (gmpxx.h) required but not found, see http://gmplib.org/])])
  AC_LANG_POP([C++])
  cvc4_cln_or_gmp=gmp
else
  CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }$CLN_CFLAGS"
  CVC4CXXFLAGS="${CVC4CXXFLAGS:+$CVC4CXXFLAGS }$CLN_CFLAGS"
  CVC4CFLAGS="${CVC4CFLAGS:+$CVC4CFLAGS }$CLN_CFLAGS"
  LIBS="$CLN_LIBS${LIBS:+ $LIBS}"
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
  # Runs the single recursive configure invocation using a relative path.
  # See https://lists.gnu.org/archive/html/autoconf/2011-04/msg00060.html
  echo "$SHELL ../../../configure ${config_cmdline[[@]]}"
  "$SHELL" "../../../configure" "${config_cmdline[[@]]}"
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
  ln -sf "$target/$build_type/config.log" "builds/config.log"
  exit $exitval
else
  AC_MSG_RESULT([this one (user-specified)])
fi

as_me=configure

# Unpack standard build types. Any particular options can be overriden with
# --enable/disable-X options
# Tim: This needs to keep CVC4CPPFLAGS, CVC4CXXFLAGS, etc. set by earlier checks
case "$with_build" in
  production) # highly optimized, no assertions, no tracing, dumping
    CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }"
    CVC4CXXFLAGS="${CVC4CXXFLAGS:+$CVC4CXXFLAGS }"
    CVC4CFLAGS="${CVC4CFLAGS:+$CVC4CFLAGS }"
    CVC4LDFLAGS="${CVC4LDFLAGS:+$CVC4LDFLAGS }"
    FLAG_VISIBILITY_HIDDEN='-fvisibility=hidden'
    if test -z "${OPTLEVEL+set}"            ; then OPTLEVEL=3                       ; fi
    if test -z "${enable_optimized+set}"    ; then enable_optimized=yes             ; fi
    if test -z "${enable_debug_symbols+set}"; then enable_debug_symbols=yes         ; fi
    if test -z "${enable_statistics+set}"   ; then enable_statistics=yes            ; fi
    if test -z "${enable_replay+set}"       ; then enable_replay=no                 ; fi
    if test -z "${enable_assertions+set}"   ; then enable_assertions=no             ; fi
    if test -z "${enable_proof+set}"        ; then enable_proof=yes                 ; fi
    if test -z "${enable_tracing+set}"      ; then enable_tracing=no                ; fi
    if test -z "${enable_dumping+set}"      ; then enable_dumping=yes               ; fi
    if test -z "${enable_muzzle+set}"       ; then enable_muzzle=no                 ; fi
    ;;
  debug) # unoptimized, debug symbols, assertions, tracing, dumping
    CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-DCVC4_DEBUG"
    CVC4CXXFLAGS="${CVC4CXXFLAGS:+$CVC4CXXFLAGS }-fno-inline"
    CVC4CFLAGS="${CVC4CFLAGS:+$CVC4CFLAGS }-fno-inline"
    CVC4LDFLAGS="${CVC4LDFLAGS:+$CVC4LDFLAGS }"
    FLAG_VISIBILITY_HIDDEN=
    if test -z "${enable_optimized+set}"    ; then enable_optimized=no              ; fi
    if test -z "${enable_debug_symbols+set}"; then enable_debug_symbols=yes         ; fi
    if test -z "${enable_statistics+set}"   ; then enable_statistics=yes            ; fi
    if test -z "${enable_replay+set}"       ; then enable_replay=yes                ; fi
    if test -z "${enable_assertions+set}"   ; then enable_assertions=yes            ; fi
    if test -z "${enable_proof+set}"        ; then enable_proof=yes                 ; fi
    if test -z "${enable_tracing+set}"      ; then enable_tracing=yes               ; fi
    if test -z "${enable_dumping+set}"      ; then enable_dumping=yes               ; fi
    if test -z "${enable_muzzle+set}"       ; then enable_muzzle=no                 ; fi
    ;;
  default) # moderately optimized, assertions, tracing, dumping
    CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }"
    CVC4CXXFLAGS="${CVC4CXXFLAGS:+$CVC4CXXFLAGS }"
    CVC4CFLAGS="${CVC4CFLAGS:+$CVC4CFLAGS }"
    CVC4LDFLAGS="${CVC4LDFLAGS:+$CVC4LDFLAGS }"
    FLAG_VISIBILITY_HIDDEN='-fvisibility=hidden'
    if test -z "${OPTLEVEL+set}"            ; then OPTLEVEL=2                       ; fi
    if test -z "${enable_optimized+set}"    ; then enable_optimized=yes             ; fi
    if test -z "${enable_debug_symbols+set}"; then enable_debug_symbols=yes         ; fi
    if test -z "${enable_statistics+set}"   ; then enable_statistics=yes            ; fi
    if test -z "${enable_replay+set}"       ; then enable_replay=yes                ; fi
    if test -z "${enable_assertions+set}"   ; then enable_assertions=yes            ; fi
    if test -z "${enable_proof+set}"        ; then enable_proof=yes                 ; fi
    if test -z "${enable_tracing+set}"      ; then enable_tracing=yes               ; fi
    if test -z "${enable_dumping+set}"      ; then enable_dumping=yes               ; fi
    if test -z "${enable_muzzle+set}"       ; then enable_muzzle=no                 ; fi
    ;;
  competition) # maximally optimized, no assertions, no tracing, no dumping, muzzled
    CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-DCVC4_COMPETITION_MODE"
    CVC4CXXFLAGS="${CVC4CXXFLAGS:+$CVC4CXXFLAGS }-funroll-all-loops -fexpensive-optimizations -fno-enforce-eh-specs"
    CVC4CFLAGS="${CVC4CFLAGS:+$CVC4CFLAGS }-funroll-all-loops -fexpensive-optimizations -fno-enforce-eh-specs"
    CVC4LDFLAGS="${CVC4LDFLAGS:+$CVC4LDFLAGS }"
    FLAG_VISIBILITY_HIDDEN='-fvisibility=hidden'
    if test -z "${OPTLEVEL+set}"            ; then OPTLEVEL=9                       ; fi
    if test -z "${enable_optimized+set}"    ; then enable_optimized=yes             ; fi
    if test -z "${enable_debug_symbols+set}"; then enable_debug_symbols=no          ; fi
    if test -z "${enable_statistics+set}"   ; then enable_statistics=no             ; fi
    if test -z "${enable_replay+set}"       ; then enable_replay=no                 ; fi
    if test -z "${enable_assertions+set}"   ; then enable_assertions=no             ; fi
    if test -z "${enable_proof+set}"        ; then enable_proof=no                  ; fi
    if test -z "${enable_tracing+set}"      ; then enable_tracing=no                ; fi
    if test -z "${enable_dumping+set}"      ; then enable_dumping=no                ; fi
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
if test "$enable_static_binary" = yes; then
  if test "$target_vendor" = apple; then
    if test -z "$MAC_STATIC_BINARY_MANUAL_OVERRIDE"; then
      AC_MSG_ERROR([[Statically-linked binaries are not supported on Mac OS.  See https://developer.apple.com/library/mac/#qa/qa2001/qa1118.html .  (If you ABSOLUTELY insist on this going forward and you know what you are doing, set MAC_STATIC_BINARY_MANUAL_OVERRIDE=1)]])
    else
      AC_MSG_WARN([MAC_STATIC_BINARY_MANUAL_OVERRIDE was set!])
      AC_MSG_WARN([Will make a static binary during this build.  Note that it may fail!])
    fi
  fi
  if test "$enable_static" != yes; then
    enable_static=yes
    AC_MSG_WARN([forcing static-library building, --enable-static-binary given])
  fi
fi

AC_MSG_CHECKING([whether to support proofs in libcvc4])

AC_ARG_ENABLE([proof],
  [AS_HELP_STRING([--disable-proof],
     [do not support proof generation])])
if test -z "${enable_proof+set}"; then
  enable_proof=yes
fi
AC_MSG_RESULT([$enable_proof])

if test "$enable_proof" = yes; then
  CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-DCVC4_PROOF"
fi
AM_CONDITIONAL([CVC4_PROOF], [test "$enable_proof" = yes])

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

AC_MSG_CHECKING([whether the replay feature should be turned on in libcvc4])

AC_ARG_ENABLE([replay],
  [AS_HELP_STRING([--disable-replay],
     [turn off the replay feature in libcvc4])])

if test -z "${enable_replay+set}"; then
  enable_replay=yes
fi

AC_MSG_RESULT([$enable_replay])

if test "$enable_replay" = yes; then
  CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-DCVC4_REPLAY"
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
else
  # turn off regular C assert() also
  CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-DNDEBUG"
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

AC_MSG_CHECKING([whether to do a dump-capable build of CVC4])
AC_ARG_ENABLE([dumping],
  [AS_HELP_STRING([--disable-dumping],
     [remove all dumping code from CVC4])])

if test -z "${enable_dumping+set}"; then
  enable_dumping=yes
fi

AC_MSG_RESULT([$enable_dumping])

if test "$enable_dumping" = yes; then
  CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-DCVC4_DUMPING"
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

# Check for libglpk (defined in config/glpk.m4)
AC_ARG_WITH([glpk],
  [AS_HELP_STRING([--with-glpk],
     [use GLPK simplex solver])], [], [with_glpk=])
CVC4_CHECK_FOR_GLPK
if test $have_libglpk -eq 1; then
  CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-DCVC4_USE_GLPK"
fi
AM_CONDITIONAL([CVC4_USE_GLPK], [test $have_libglpk -eq 1])
AC_SUBST([GLPK_LDFLAGS])
AC_SUBST([GLPK_LIBS])

# Build with libabc (defined in config/abc.m4)
AC_ARG_WITH([abc],
  [AS_HELP_STRING([--with-abc],
     [use the ABC AIG library])], [], [with_abc=])
CVC4_CHECK_FOR_ABC
if test $have_libabc -eq 1; then
  CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-DCVC4_USE_ABC"
fi
AM_CONDITIONAL([CVC4_USE_ABC], [test $have_libabc -eq 1])
AC_SUBST([ABC_LDFLAGS])
AC_SUBST([ABC_LIBS])


# Build with libcryptominisat
AC_ARG_WITH([cryptominisat],
  [AS_HELP_STRING([--with-cryptominisat],
     [use the CRYPTOMINISAT sat solver])], [], [with_cryptominisat=])
CVC4_CHECK_FOR_CRYPTOMINISAT
if test $have_libcryptominisat -eq 1; then
  CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-DCVC4_USE_CRYPTOMINISAT"
  CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-I$CRYPTOMINISAT_HOME/install/include"
fi
AM_CONDITIONAL([CVC4_USE_CRYPTOMINISAT], [test $have_libcryptominisat -eq 1])
AC_SUBST([CRYPTOMINISAT_LDFLAGS])
AC_SUBST([CRYPTOMINISAT_LIBS])


# Check to see if this version/architecture of GNU C++ explicitly
# instantiates __gnu_cxx::hash<uint64_t> or not.  Some do, some don't.
# See src/util/hash.h.
AC_MSG_CHECKING([whether __gnu_cxx::hash<uint64_t> is already specialized])
AC_LANG_PUSH([C++])
AC_COMPILE_IFELSE([AC_LANG_SOURCE([
#include <stdint.h>
#include <ext/hash_map>
namespace __gnu_cxx { template<> struct hash<uint64_t> {}; }])],
                  [AC_MSG_RESULT([no]); CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-DCVC4_NEED_HASH_UINT64_T"],
                  [AC_MSG_RESULT([yes])])
AC_LANG_POP([C++])

# Check whether "long" and "int64_t" are distinct types w.r.t. overloading.
# Even if they have the same size, they can be distinct, and some platforms
# can have problems with ambiguous function calls when auto-converting
# int64_t to long, and others will complain if you overload a function
# that takes an int64_t with one that takes a long (giving a redefinition
# error).  So we have to keep both happy.  Probably the same underlying
# issue as the hash specialization above, but let's check separately
# for flexibility.
AC_MSG_CHECKING([for the relationship between long and int64_t])
AC_LANG_PUSH([C++])
AC_COMPILE_IFELSE([AC_LANG_SOURCE([
#include <stdint.h>
void foo(long) {}
void foo(int64_t) {}])],
                  [AC_MSG_RESULT([no relationship detected]); CVC4_NEED_INT64_T_OVERLOADS=1],
                  [AC_MSG_RESULT([typedef or similar]); CVC4_NEED_INT64_T_OVERLOADS=0])
AC_LANG_POP([C++])
AC_SUBST([CVC4_NEED_INT64_T_OVERLOADS])

# Check for ANTLR runantlr script (defined in config/antlr.m4)
AC_PROG_ANTLR

CVC4_CXX_OPTION([-Werror], [WERROR])
CVC4_C_OPTION([-Werror], [C_WERROR])
CVC4_CXX_OPTION([-Wno-deprecated], [WNO_DEPRECATED])
CVC4_C_OPTION([-Wno-deprecated], [C_WNO_DEPRECATED])
CVC4_CXX_OPTION([-Wno-conversion-null], [WNO_CONVERSION_NULL])
CVC4_CXX_OPTION([-Wno-tautological-compare], [WNO_TAUTOLOGICAL_COMPARE])
CVC4_CXX_OPTION([-Wno-parentheses], [WNO_PARENTHESES])
CVC4_CXX_OPTION([-Wno-uninitialized], [WNO_UNINITIALIZED])
CVC4_CXX_OPTION([-Wno-unused-variable], [WNO_UNUSED_VARIABLE])
CVC4_CXX_OPTION([-fno-strict-aliasing], [FNO_STRICT_ALIASING])
AC_SUBST([WERROR])
AC_SUBST([WNO_CONVERSION_NULL])
AC_SUBST([WNO_TAUTOLOGICAL_COMPARE])
AC_SUBST([WNO_PARENTHESES])
AC_SUBST([WNO_UNINITIALIZED])
AC_SUBST([WNO_UNUSED_VARIABLE])
AC_SUBST([FNO_STRICT_ALIASING])

# On Mac, we have to fix the visibility of standard library symbols.
# Otherwise, exported template instantiations---even though explicitly
# CVC4_PUBLIC, can be generated as symbols with internal-only linkage.
# Presumably, Apple is distributing a libstdc++ that is built *without*
# --enable-libstdcxx-visibility (?)
if test "$target_vendor" = apple; then
  CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-D_GLIBCXX_VISIBILITY_DEFAULT=\"__attribute__((__visibility__(\\\"default\\\")))\""
fi

# Tell top-level Makefile to include $(top_srcdir)/personal.mk
AC_ARG_ENABLE([personal-make-rules],
  [AS_HELP_STRING([--enable-personal-make-rules],
     [include top-level personal.mk (if it exists)])])
if test "$enable_personal_make_rules" = yes; then
  # This allows us to include a personal.mk makefile from every
  # generated makefile.  Named zz_* in order to make sure this
  # comes last, so it gets other definitions (in particular top_srcdir).
  zz_cvc4_use_personal_make_rules='yes

all:;
include $(top_srcdir)/personal.mk
$(top_srcdir)/personal.mk:; @touch "$@"'
  AC_SUBST([zz_cvc4_use_personal_make_rules])
fi

# Doxygen configuration
AC_ARG_ENABLE([internals-documentation],
  [AS_HELP_STRING([--enable-internals-documentation],
     [build Doxygen documentation for static and private member functions])])
if test "$enable_internals_documentation" = yes; then
  DOXYGEN_EXTRACT_PRIVATE=YES
  DOXYGEN_EXTRACT_STATIC=YES
else
  DOXYGEN_EXTRACT_PRIVATE=NO
  DOXYGEN_EXTRACT_STATIC=NO
fi
AC_SUBST([DOXYGEN_EXTRACT_PRIVATE])
AC_SUBST([DOXYGEN_EXTRACT_STATIC])

DX_MAN_FEATURE(OFF)
DX_PDF_FEATURE(OFF)
DX_PS_FEATURE(OFF)
DX_DOT_FEATURE(OFF)
DX_INIT_DOXYGEN($PACKAGE_NAME, config/doxygen.cfg, $srcdir/doc/doxygen)

AC_ARG_ENABLE([unit-testing], AS_HELP_STRING([--disable-unit-testing], [don't build support for unit testing, even if available]), , [enable_unit_testing=check])
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

TESTS_ENVIRONMENT=
RUN_REGRESSION_ARGS=
if test "$enable_proof" = yes; then
  RUN_REGRESSION_ARGS="${RUN_REGRESSION_ARGS:+$RUN_REGRESSION_ARGS }--proof"
fi
AC_SUBST([TESTS_ENVIRONMENT])
AC_SUBST([RUN_REGRESSION_ARGS])

CXXTESTGEN=
AC_PATH_PROG(CXXTESTGEN, cxxtestgen.pl, [], [$CXXTEST:$PATH])
if test -z "$CXXTESTGEN"; then
  AC_PATH_PROG(CXXTESTGEN, cxxtestgen.py, [], [$CXXTEST:$PATH])
fi
if test -z "$CXXTESTGEN"; then
  AC_PATH_PROG(CXXTESTGEN, cxxtestgen, [], [$CXXTEST:$PATH])
fi
# The latest version of cxxtest distributed from the git repository places
# cxxtest under <cxxtest-root>/bin/cxxtest
if test -z "$CXXTESTGEN"; then
  AC_PATH_PROG(CXXTESTGEN, cxxtestgen, [], [$CXXTEST/bin:$PATH])
fi
if test "$enable_unit_testing" = "no"; then
  AC_MSG_NOTICE([unit tests disabled by user request.])
  CXXTESTGEN=
  CXXTEST=
elif test -z "$CXXTESTGEN"; then
  AC_MSG_NOTICE([unit tests disabled, could not find cxxtestgen.pl or cxxtestgen.py or cxxtestgen])
elif test -z "$CXXTEST"; then
  CXXTEST=`dirname "$CXXTESTGEN"`
  AC_MSG_CHECKING([for location of CxxTest headers])
  if test -e "$CXXTEST/cxxtest/TestRunner.h"; then
    AC_MSG_RESULT([$CXXTEST])
  else
    if test -e "/usr/include/cxxtest/TestRunner.h"; then
      AC_MSG_RESULT([/usr/include])
    else
      AC_MSG_RESULT([not found])
      AC_MSG_WARN([unit tests disabled, CxxTest headers not found.])
      CXXTESTGEN=
      CXXTEST=
    fi
  fi
fi

if test "$enable_unit_testing" = yes -a -z "$CXXTESTGEN"; then
  AC_MSG_ERROR([--enable-unit-testing given but cxxtest not found.])
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

AC_ARG_VAR(PYTHON, [PYTHON interpreter (used for building legacy Java library interface)])

if test -z "$PYTHON"; then
  AC_CHECK_PROGS(PYTHON, python, python, [])
else
  AC_CHECK_PROG(PYTHON, "$PYTHON", "$PYTHON", [])
fi

if test -z "$PYTHON"; then
  AC_MSG_WARN([python not found, cannot build libcvc4compat_java (the legacy Java interface).])
  CXXTESTGEN=
  CXXTEST=
fi

# Checks for libraries.

AC_SEARCH_LIBS([clock_gettime], [rt pthread],
               [AC_DEFINE([HAVE_CLOCK_GETTIME], [1],
                          [Defined to 1 if clock_gettime() is supported by the platform.])],
               [AC_LIBOBJ([clock_gettime])])
AC_CHECK_FUNC([strtok_r], [AC_DEFINE([HAVE_STRTOK_R], [1],
                                     [Defined to 1 if strtok_r() is supported by the platform.])])
AC_CHECK_FUNC([ffs], [AC_DEFINE([HAVE_FFS], [1],
                                [Defined to 1 if ffs() is supported by the platform.])])

AC_LIBOBJ([strtok_r ffs])

# Check for antlr C++ runtime (defined in config/antlr.m4)
AC_LIB_ANTLR

# Check for user preferences for language bindings to build, and for
# build support.  The arg list is the default set if unspecified by
# the user (the actual built set is the subset that appears to be
# supported by the build host).
CVC4_CHECK_BINDINGS([c java])dnl csharp perl php python ruby tcl ocaml])

# Checks for header files and their contents.
AC_CHECK_HEADERS([getopt.h unistd.h ext/stdio_filebuf.h])

# Checks for typedefs, structures, and compiler characteristics.
#AC_HEADER_STDBOOL
# these are bad macros, they clash with system header <stdint.h> !!
#AC_TYPE_UINT16_T
#AC_TYPE_UINT32_T
#AC_TYPE_UINT64_T
#AC_TYPE_SIZE_T

# guard against double-inclusion of the autoheader
AH_TOP([#ifndef __CVC4__CVC4AUTOCONFIG_H
#define __CVC4__CVC4AUTOCONFIG_H])
AH_BOTTOM([#endif /* __CVC4__CVC4AUTOCONFIG_H */])

AC_CHECK_DECLS([optreset], [], [], [#include <getopt.h>])

# check with which standard strerror_r() complies
AC_FUNC_STRERROR_R

# is is_sorted() in std or __gnu_cxx?
CHECK_FOR_IS_SORTED

# require boost library
BOOST_REQUIRE()

# look for boost threading library
AC_ARG_WITH([portfolio],
    AS_HELP_STRING([--with-portfolio], [build the multithreaded portfolio version of CVC4 (pcvc4)]))
cvc4_save_LDFLAGS="$LDFLAGS"
if test "$enable_static_binary" = yes; then
  LDFLAGS="-static $LDFLAGS"
fi
cvc4_has_threads=yes
AC_ARG_ENABLE([thread-support],
    AS_HELP_STRING([--disable-thread-support], [do not support multithreaded-capable library]))
if test "$enable_thread_support" = no; then
  cvc4_has_threads=no
  if test "$with_portfolio" = yes; then
    AC_MSG_ERROR([user gave both --with-portfolio and --disable-thread-support, which are contradictory])
  fi
else
  BOOST_THREADS([], [AC_MSG_WARN([disabling multithreaded support])
                     cvc4_has_threads=no])
fi
LDFLAGS="$cvc4_save_LDFLAGS"
if test $cvc4_has_threads = no; then
  if test "$enable_thread_support" = yes; then
    AC_MSG_ERROR([user gave --enable-thread-support but could not build with threads; maybe boost threading library is missing?])
  fi
  if test "$with_portfolio" = yes; then
    AC_MSG_ERROR([user gave --with-portfolio but could not build with threads; maybe boost threading library is missing?])
  fi
  with_portfolio=no
fi
if test "$with_portfolio" != yes; then
  with_portfolio=no
fi
AM_CONDITIONAL([CVC4_BUILD_PCVC4], [test "$with_portfolio" = yes])
if test "$with_portfolio" = yes; then
  CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-DCVC4_PORTFOLIO"

  # see if Boost has thread attributes (should be any version >= 1.50.0)
  # non-fatal error if not, but we won't support --thread-stack option
  AC_MSG_CHECKING([whether Boost threads support thread attrs])
  AC_LANG_PUSH([C++])
  cvc4_save_CPPFLAGS="$CPPFLAGS"
  cvc4_save_LIBS="$LIBS"
  cvc4_save_LDFLAGS="$LDFLAGS"
  CPPFLAGS="$CPPFLAGS $BOOST_CPPFLAGS"
  LIBS="$LIBS $BOOST_THREAD_LIBS"
  LDFLAGS="$LDFLAGS $BOOST_THREAD_LDFLAGS"
  AC_LINK_IFELSE([AC_LANG_PROGRAM([#include <boost/thread.hpp>],
         [boost::thread::attributes attrs; attrs.set_stack_size(10 * 1024 * 1024);])],
    [cvc4_boost_has_thread_attr=1;
     AC_MSG_RESULT([yes])],
    [cvc4_boost_has_thread_attr=0;
     AC_MSG_RESULT([no])])
  CPPFLAGS="$cvc4_save_CPPFLAGS"
  LIBS="$cvc4_save_LIBS"
  LDFLAGS="$cvc4_save_LDFLAGS"
  AC_LANG_POP([C++])
else
  cvc4_boost_has_thread_attr=0
fi
AC_DEFINE_UNQUOTED([BOOST_HAS_THREAD_ATTR], $cvc4_boost_has_thread_attr, [Define to 1 if Boost threading library has support for thread attributes])

# Check for libreadline (defined in config/readline.m4)
AC_ARG_WITH([readline], [AS_HELP_STRING([--with-readline], [support the readline library])], [], [with_readline=check])
# make the flags as close as possible to the final flags, because the Boost
# flags can bring in a different, incompatible readline library than we'd
# get otherwise (e.g. on Mac, where there are commonly two different readlines,
# one in /usr and one in /opt/local)
cvc4_rlcheck_save_CPPFLAGS="$CPPFLAGS"
cvc4_rlcheck_save_CXXFLAGS="$CXXFLAGS"
cvc4_rlcheck_save_CFLAGS="$CFLAGS"
cvc4_rlcheck_save_LDFLAGS="$LDFLAGS"
CPPFLAGS="${CPPFLAGS:+$CPPFLAGS }${BOOST_CPPFLAGS:+$BOOST_CPPFLAGS }$CVC4CPPFLAGS"
CXXFLAGS="${CXXFLAGS:+$CXXFLAGS }$CVC4CXXFLAGS $WNO_DEPRECATED"
CFLAGS="${CFLAGS:+$CFLAGS }$CVC4CFLAGS $C_WNO_DEPRECATED -fexceptions"
LDFLAGS="${LDFLAGS:+$LDFLAGS }$CVC4LDFLAGS"
CVC4_CHECK_FOR_READLINE
CPPFLAGS="$cvc4_rlcheck_save_CPPFLAGS"
CXXFLAGS="$cvc4_rlcheck_save_CXXFLAGS"
CFLAGS="$cvc4_rlcheck_save_CFLAGS"
LDFLAGS="$cvc4_rlcheck_save_LDFLAGS"
AC_DEFINE_UNQUOTED([HAVE_LIBREADLINE], $have_libreadline, [Define to 1 to use libreadline])
AC_DEFINE_UNQUOTED([READLINE_COMPENTRY_FUNC_RETURNS_CHARP], $readline_compentry_func_returns_charp, [Define to 1 if rl_completion_entry_function is declared to return pointer to char])
AC_SUBST([READLINE_LIBS])

# Whether to build compatibility library
CVC4_BUILD_LIBCOMPAT=yes
AC_ARG_WITH([compat],
    AS_HELP_STRING([--with-compat], [build compatibility library (CVC3 API layer)]),
    [if test "$withval" = no; then CVC4_BUILD_LIBCOMPAT=no; fi])
AC_MSG_CHECKING([whether to build compatibility library (CVC3 API layer)])
if test "$CVC4_BUILD_LIBCOMPAT" = yes; then
  AC_MSG_RESULT([yes])
else
  AC_MSG_RESULT([no, disabled by user])
fi
AC_SUBST(CVC4_BUILD_LIBCOMPAT)
AM_CONDITIONAL([CVC4_BUILD_LIBCOMPAT], [test "$CVC4_BUILD_LIBCOMPAT" = yes])

# Check for availability of TLS support (e.g. __thread storage class)
AC_MSG_CHECKING([whether to use compiler-supported TLS if available])
AC_ARG_ENABLE([tls], AS_HELP_STRING([--disable-tls], [don't use compiler-native TLS]))
if test $cvc4_has_threads = no; then
  # We disable TLS entirely by simply telling the build system that
  # the empty string is the __thread keyword.
  AC_MSG_RESULT([multithreading disabled])
  CVC4_TLS_SUPPORTED=1
  CVC4_TLS=
  CVC4_TLS_explanation='disabled (no multithreading support)'
else
  if test -z "${enable_tls+set}" || test "$enable_tls" = "yes"; then
    AC_MSG_RESULT([yes])
    AX_TLS([CVC4_TLS=$ac_cv_tls], [CVC4_TLS=])
  else
    AC_MSG_RESULT([no])
    CVC4_TLS=
  fi
  if test -n "$CVC4_TLS"; then
    CVC4_TLS_SUPPORTED=1
    CVC4_TLS_explanation="$CVC4_TLS"
  else
    CVC4_TLS_explanation='pthread_getspecific()'
    CVC4_TLS_SUPPORTED=0
  fi
fi
AC_SUBST([CVC4_TLS])
AC_SUBST([CVC4_TLS_SUPPORTED])

# Whether to compile with google profiling tools
cvc4_use_google_perftools=0
AC_ARG_WITH(
    [google_perftools],
    AS_HELP_STRING(
        [--with-google-perftools],
        [use Google Performance Tools]
    ),
    [if test "$withval" != no; then
        cvc4_use_google_perftools=1
     fi
    ]
)
AC_MSG_CHECKING([whether to link in google perftools libraries])
if test $cvc4_use_google_perftools = 1; then
  AC_MSG_RESULT([yes])
  AC_CHECK_LIB([tcmalloc], [MallocExtension_GetAllocatedSize], , [AC_MSG_ERROR([cannot link google-perftools test program with -ltcmalloc])], [-lpthread])
  AC_CHECK_LIB([profiler], [ProfilerStart], , [AC_MSG_ERROR([cannot link google-perftools test program with -lprofiler])], [-lpthread])
else
  AC_MSG_RESULT([no (user didn't request it)])
fi

# Java
AC_ARG_VAR(JAVA, [Java interpreter (used when testing Java interface)])
AC_ARG_VAR(JAVAC, [Java compiler (used when building and testing Java interface)])
AC_ARG_VAR(JAVAH, [Java compiler (used when building and testing Java interface)])
AC_ARG_VAR(JAR, [Jar archiver (used when building Java interface)])
if test "$cvc4_build_java_bindings"; then
  dnl AM_PROG_GCJ
  if test -z "$JAVA"; then
    AC_CHECK_PROGS(JAVA, java, java, [])
  else
    AC_CHECK_PROG(JAVA, "$JAVA", "$JAVA", [])
  fi
  if test -z "$JAVAC"; then
    AC_CHECK_PROGS(JAVAC, javac gcj, javac, [])
    if test "$JAVAC" = gcj; then JAVAC='gcj -C'; fi
  else
    AC_CHECK_PROG(JAVAC, "$JAVAC", "$JAVAC", [])
  fi
  if test -z "$JAVAH"; then
    AC_CHECK_PROGS(JAVAH, javah gcjh, javah, [])
  else
    AC_CHECK_PROG(JAVAH, "$JAVAH", "$JAVAH", [])
  fi
  if test -z "$JAR"; then
    AC_CHECK_PROGS(JAR, jar, jar, [])
  else
    AC_CHECK_PROG(JAR, "$JAR", "$JAR", [])
  fi
fi

# on Mac OS X, Java doesn't like the .so module extension; it wants .dylib
module=no eval CVC4_JAVA_MODULE_EXT="$shrext_cmds"
if test -z "$CVC4_JAVA_MODULE_EXT"; then
  CVC4_JAVA_MODULE_EXT=.so
fi
AC_SUBST([CVC4_JAVA_MODULE_EXT])

# Prepare configure output

if test "$enable_shared" = yes; then BUILDING_SHARED=1; else BUILDING_SHARED=0; fi
if test "$enable_static" = yes; then BUILDING_STATIC=1; else BUILDING_STATIC=0; fi
if test "$enable_static_binary" = yes; then STATIC_BINARY=1; else STATIC_BINARY=0; fi
AC_SUBST(BUILDING_SHARED)
AC_SUBST(BUILDING_STATIC)
AC_SUBST(STATIC_BINARY)
AM_CONDITIONAL([STATIC_BINARY], [test "$enable_static_binary" = yes])
AM_CONDITIONAL([COVERAGE_ENABLED], [test "$enable_coverage" = yes])

AM_CONDITIONAL([CVC4_DEBUG], [test "$with_build" = debug])
AM_CONDITIONAL([CVC4_TRACING], [test "$enable_tracing" = yes])

AC_SUBST(CVC4_LIBRARY_VERSION)
AC_SUBST(CVC4_PARSER_LIBRARY_VERSION)
AC_SUBST(CVC4_COMPAT_LIBRARY_VERSION)
AC_SUBST(CVC4_BINDINGS_LIBRARY_VERSION)

AC_DEFINE_UNQUOTED(CVC4_MAJOR, ${CVC4_MAJOR}, [Major component of the version of CVC4.])
AC_DEFINE_UNQUOTED(CVC4_MINOR, ${CVC4_MINOR}, [Minor component of the version of CVC4.])
AC_DEFINE_UNQUOTED(CVC4_RELEASE, ${CVC4_RELEASE}, [Release component of the version of CVC4.])
AC_DEFINE_UNQUOTED(CVC4_EXTRAVERSION, ["${CVC4_EXTRAVERSION}"], [Extraversion component of the version of CVC4.])
AC_DEFINE_UNQUOTED(CVC4_RELEASE_STRING, ["${CVC4_RELEASE_STRING}"], [Full release string for CVC4.])

CPPFLAGS="${CPPFLAGS:+$CPPFLAGS }${BOOST_CPPFLAGS:+$BOOST_CPPFLAGS }$CVC4CPPFLAGS"
CXXFLAGS="${CXXFLAGS:+$CXXFLAGS }$CVC4CXXFLAGS -Wno-deprecated"
CFLAGS="${CFLAGS:+$CFLAGS }$CVC4CFLAGS -Wno-deprecated -fexceptions"
LDFLAGS="${LDFLAGS:+$LDFLAGS }$CVC4LDFLAGS"

# visibility flag not supported for Windows builds
# also increase default stack size for Windows binaries
case $host_os in
  (*mingw*) FLAG_VISIBILITY_HIDDEN=
            cvc4_LDFLAGS=-Wl,--stack,134217728
            pcvc4_LDFLAGS=-Wl,--stack,134217728
esac

AC_SUBST(FLAG_VISIBILITY_HIDDEN)
AC_SUBST(cvc4_LDFLAGS)
AC_SUBST(pcvc4_LDFLAGS)

AM_CONDITIONAL(WHITE_AND_BLACK_TESTS, [test -z "$FLAG_VISIBILITY_HIDDEN"])

# remember the command line used for configure
AC_SUBST(cvc4_config_cmdline)

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
# Similar trickery for "if"
mk_if=if
AC_SUBST(mk_if)
mk_empty=
AC_SUBST(mk_empty)

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

# month/year for man pages
MAN_DATE=`date '+%B %Y'`
AC_SUBST(MAN_DATE)

AC_CONFIG_FILES([
  Makefile.builds
  Makefile
  proofs/signatures/Makefile]
  m4_esyscmd([find contrib src test examples -name Makefile.am | grep -v '^contrib/theoryskel/' | grep -v '^contrib/alttheoryskel/' | sort | sed 's,\.am$,,'])
)

if test $cvc4_has_threads = yes; then
  support_multithreaded='with boost threading library'
  AM_CONDITIONAL([CVC4_HAS_THREADS], [true])
  AC_SUBST([CVC4_HAS_THREADS], 1)
else
  support_multithreaded='no'
  AM_CONDITIONAL([CVC4_HAS_THREADS], [false])
  AC_SUBST([CVC4_HAS_THREADS], 0)
fi

# Final information to the user
gpl=no
licensewarn=

if test "$custom_build_profile" = yes; then
  with_build="$with_build (customized)"
fi

support_unit_tests='cxxtest not found; unit tests not supported'
if test -n "$CXXTEST"; then
  support_unit_tests='unit testing infrastructure enabled in build directory'
elif test "$enable_unit_testing" = no; then
  support_unit_tests='unit testing disabled by user'
fi

if test "$enable_optimized" = yes; then
  optimized="yes, at level $OPTLEVEL"
else
  optimized="no"
fi

if test $have_libglpk -eq 1; then
  gpl=yes
  gpllibs="${gpllibs} glpk"
fi

if test $have_libreadline -eq 1; then
  gpl=yes
  gpllibs="${gpllibs} readline"
fi

if test $cvc4_cln_or_gmp = cln; then
  mplibrary='cln (GPL)'
  gpl=yes
  gpllibs="${gpllibs} cln"
  if test $with_portfolio = yes; then
    AC_ERROR([Bad configuration detected: cannot build portfolio with CLN.
Please specify only one of --with-portfolio and --with-cln.])
  fi
else
  mplibrary='gmp'
fi

if test "$gpl" = yes; then
  if test "$CVC4_BSD_LICENSED_CODE_ONLY" = 1; then
    AC_ERROR([Bad configuration detected: BSD-licensed code only, but also requested GPLed libraries:$gpllibs
To permit GPL'ed dependences, use the configure flag --enable-gpl])
  fi

  licensewarn="${licensewarn}"'****************************************************************************
Please note that CVC4 will be built against the following GPLed libraries:
 '"$gpllibs"'
As these libraries are covered under the GPLv3, so is this build of CVC4.
CVC4 is also available to you under the terms of the (modified) BSD license.
If you prefer to license CVC4 under those terms, please configure with the
option "--bsd", which will disable all optional GPLed library dependences.
****************************************************************************

'
  license="GPLv3 (due to optional libraries; see below)"
else
  licensewarn="${licensewarn}Please note that this configuration is NOT built against any GPL'ed
libraries, so it is covered by the (modified) BSD license.  This is,
however, not the best-performing configuration of CVC4.  To build
against GPL'ed libraries which improve CVC4's performance, re-configure
with '--best --enable-gpl'.

"
  license="modified BSD"
fi

if test "$gpl" = yes; then isgpl=1; else isgpl=0; fi
AC_DEFINE_UNQUOTED(CVC4_GPL_DEPS, $isgpl, [Whether CVC4 is built with the (optional) GPLed library dependences.])

CVC4_COMPAT_LIBRARY_VERSION_or_nobuild="$CVC4_COMPAT_LIBRARY_VERSION"
CVC4_BINDINGS_LIBRARY_VERSION_or_nobuild="$CVC4_BINDINGS_LIBRARY_VERSION"
if test "$CVC4_BUILD_LIBCOMPAT" = no; then
  CVC4_COMPAT_LIBRARY_VERSION_or_nobuild="N/A"
fi
if test -z "$CVC4_LANGUAGE_BINDINGS"; then
  CVC4_BINDINGS_LIBRARY_VERSION_or_nobuild="N/A"
fi

bindings_to_be_built=none
if test -n "$CVC4_LANGUAGE_BINDINGS"; then
  bindings_to_be_built="$CVC4_LANGUAGE_BINDINGS"
  if test -z "$SWIG"; then
    bindings_to_be_built="$bindings_to_be_built (for CVC3 compatibility layer only; SWIG not found)"
  fi
fi

CVC4_CONFIG_FILE_ONLY_IF_CHANGED([src/base/tls.h])
CVC4_CONFIG_FILE_ONLY_IF_CHANGED([src/util/integer.h])
CVC4_CONFIG_FILE_ONLY_IF_CHANGED([src/util/rational.h])

CVC4_CONFIG_FILE_ONLY_IF_CHANGED([doc/cvc4.1_template])
CVC4_CONFIG_FILE_ONLY_IF_CHANGED([doc/cvc4.5])
CVC4_CONFIG_FILE_ONLY_IF_CHANGED([doc/libcvc4.3_template])
CVC4_CONFIG_FILE_ONLY_IF_CHANGED([doc/SmtEngine.3cvc_template])
CVC4_CONFIG_FILE_ONLY_IF_CHANGED([doc/options.3cvc_template])
CVC4_CONFIG_FILE_ONLY_IF_CHANGED([doc/libcvc4parser.3])
CVC4_CONFIG_FILE_ONLY_IF_CHANGED([doc/libcvc4compat.3])

AC_OUTPUT

cat <<EOF

CVC4 $VERSION

Build profile: $with_build
Build ID     : $build_type
Optimized    : $optimized
Debug symbols: $enable_debug_symbols
Proofs       : $enable_proof
Statistics   : $enable_statistics
Replay       : $enable_replay
Assertions   : $enable_assertions
Tracing      : $enable_tracing
Dumping      : $enable_dumping
Muzzle       : $enable_muzzle

Unit tests   : $support_unit_tests
gcov support : $enable_coverage
gprof support: $enable_profiling

Static libs  : $enable_static
Shared libs  : $enable_shared
Static binary: $enable_static_binary
Compat lib   : $CVC4_BUILD_LIBCOMPAT
Bindings     : $bindings_to_be_built

Multithreaded: $support_multithreaded
TLS support  : $CVC4_TLS_explanation
Portfolio    : $with_portfolio

MP library   : $mplibrary
GLPK         : $with_glpk
ABC          : $with_abc
Readline     : $with_readline

CPPFLAGS     : $CPPFLAGS
CXXFLAGS     : $CXXFLAGS
CFLAGS       : $CFLAGS
LIBS         : $LIBS
LDFLAGS      : $LDFLAGS

libcvc4 version        : $CVC4_LIBRARY_VERSION
libcvc4parser version  : $CVC4_PARSER_LIBRARY_VERSION
libcvc4compat version  : $CVC4_COMPAT_LIBRARY_VERSION_or_nobuild
libcvc4bindings version: $CVC4_BINDINGS_LIBRARY_VERSION_or_nobuild

Install into : $prefix

CVC4 license : $license

${licensewarn}Now just type make, followed by make check or make install, as you like.

EOF

if test -n "$CVC4_UNSUPPORTED_LANGUAGE_BINDINGS"; then
  AC_MSG_WARN([])
  AC_MSG_WARN([You are electing to build unsupported language binding(s):])
  AC_MSG_WARN([    $CVC4_UNSUPPORTED_LANGUAGE_BINDINGS])
  AC_MSG_WARN([Please be aware that these bindings may not compile, or])
  AC_MSG_WARN([work, and the interface to CVC4 via these bindings may])
  AC_MSG_WARN([change drastically in upcoming releases of CVC4.])
  AC_MSG_WARN([])
fi

if test -n "$CVC4_INTEGRITY_WARNING"; then
  AC_MSG_WARN([])
  AC_MSG_WARN($CVC4_INTEGRITY_WARNING)
  AC_MSG_WARN([Please run "make check" after building to ensure integrity of the binary and library])
  AC_MSG_WARN([])
fi
