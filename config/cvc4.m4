# CVC4_AC_INIT
# ------------
# Do early initialization/diversion of autoconf things for CVC4 build process.
AC_DEFUN([CVC4_AC_INIT],
dnl _AS_ME_PREPARE
[CVC4_REWRITE_ARGS_FOR_BUILD_PROFILE
])# CVC4_AC_INIT


# CVC4_REWRITE_ARGS_FOR_BUILD_PROFILE
# -----------------------------------
# Rewrite (e.g.) "./configure debug" to "./configure --with-build=debug"
AC_DEFUN([CVC4_REWRITE_ARGS_FOR_BUILD_PROFILE],
[m4_divert_push([PARSE_ARGS])dnl

CVC4_BSD_LICENSED_CODE_ONLY=1

m4_divert_once([HELP_ENABLE], [[
Licensing and performance options:
  --bsd                   disable all GPL dependences (default)
  --enable-gpl            permit GPL dependences, if available
  --best                  turn on dependences known to give best performance]])dnl

handle_option() {
  ac_option="$[]1"
  case $ac_option in
    --bsd|--disable-gpl|CVC4_BSD_LICENSED_CODE_ONLY=1)
      if test "$CVC4_LICENSE_OPTION" = gpl; then AC_ERROR([cannot give both --bsd and --enable-gpl]); fi
      CVC4_LICENSE_OPTION=bsd
      ac_option="CVC4_BSD_LICENSED_CODE_ONLY=1"
      eval $ac_option
      ;;
    --enable-gpl|--gpl|CVC4_BSD_LICENSED_CODE_ONLY=0)
      if test "$CVC4_LICENSE_OPTION" = bsd; then AC_ERROR([cannot give both --bsd and --enable-gpl]); fi
      CVC4_LICENSE_OPTION=gpl
      ac_option="CVC4_BSD_LICENSED_CODE_ONLY=0"
      eval $ac_option
      ;;
    --best)
      # set the best configuration
      handle_option --with-readline
      handle_option --with-cln
      handle_option --with-glpk
      handle_option --with-abc
      return
      ;;
    -enable-proofs|--enable-proofs)
      ac_option='--enable-proof'
      ;;
    -*|*=*)
      ;;
    production|production-*|debug|debug-*|competition|competition-*)
      # regexp `\?' not supported on Mac OS X
      ac_option_build=`expr "$ac_option" : '\([[^-]]*\)-\{0,1\}'`
      ac_cvc4_build_profile_set=yes
      as_me=configure
      AC_MSG_NOTICE([CVC4: building profile $ac_option_build])
      for x in optimized proof statistics replay assertions tracing dumping muzzle coverage profiling; do
        if expr "$ac_option" : '.*-no'$x'$' >/dev/null || expr "$ac_option" : '.*-no'$x'-' >/dev/null; then
          eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--disable-$x\""'
        fi
        if expr "$ac_option" : '.*-'$x'$' >/dev/null || expr "$ac_option" : '.*-'$x'-' >/dev/null; then
          eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--enable-$x\""'
        fi
      done
      if expr "$ac_option" : '.*-nostaticbinary$' >/dev/null || expr "$ac_option" : '.*-nostaticbinary-' >/dev/null; then
        eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--disable-static-binary\""'
      fi
      if expr "$ac_option" : '.*-staticbinary$' >/dev/null || expr "$ac_option" : '.*-staticbinary-' >/dev/null; then
        eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--enable-static-binary\""'
      fi
      if expr "$ac_option" : '.*-nodebugsymbols$' >/dev/null || expr "$ac_option" : '.*-nodebugsymbols-' >/dev/null; then
        eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--disable-debug-symbols\""'
      fi
      if expr "$ac_option" : '.*-debugsymbols$' >/dev/null || expr "$ac_option" : '.*-debugsymbols-' >/dev/null; then
        eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--enable-debug-symbols\""'
      fi
      if expr "$ac_option" : '.*-noglpk' >/dev/null || expr "$ac_option" : '.*-noglpk-' >/dev/null; then
        eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--without-glpk\""'
      fi
      if expr "$ac_option" : '.*-glpk' >/dev/null || expr "$ac_option" : '.*-glpk-' >/dev/null; then
        eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--with-glpk\""'
      fi
      if expr "$ac_option" : '.*-noabc' >/dev/null || expr "$ac_option" : '.*-noabc-' >/dev/null; then
        eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--without-abc\""'
      fi
      if expr "$ac_option" : '.*-abc' >/dev/null || expr "$ac_option" : '.*-abc-' >/dev/null; then
        eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--with-abc\""'
      fi
      for x in cln gmp; do
        if expr "$ac_option" : '.*-no'$x'$' >/dev/null || expr "$ac_option" : '.*-no'$x'-' >/dev/null; then
          eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--without-$x\""'
        fi
        if expr "$ac_option" : '.*-'$x'$' >/dev/null || expr "$ac_option" : '.*-'$x'-' >/dev/null; then
          eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--with-$x\""'
        fi
      done
      ac_option="--with-build=$ac_option_build"
  esac
  eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }'\'\$ac_option\'\"
}

unset ac_cvc4_rewritten_args
for ac_option
do
  if test "$ac_option" = personal; then
    if test -e personal.conf; then
      handle_option --enable-personal-make-rules
      while read arg; do
        handle_option "$arg"
      done < personal.conf
    else
      AC_MSG_ERROR([personal build profile selected, but cannot find personal.conf])
    fi
  else
    handle_option "$ac_option"
  fi
done
eval set x $ac_cvc4_rewritten_args
shift
dnl echo "args are now:" "${@}"
m4_divert_pop([PARSE_ARGS])dnl
])# CVC4_REWRITE_ARGS_FOR_BUILD_PROFILE


# CVC4_COPY_IF_CHANGED(FROM, TO)
# ------------------------------
# Copy file FROM to TO, if they have textual differences.
AC_DEFUN([CVC4_COPY_IF_CHANGED], [
if diff -q "$1" "$2" >/dev/null 2>&1; then
  dnl they are the same
  :
else
  dnl they are different
  cp "$1" "$2"
fi
])# CVC4_COPY_IF_CHANGED


# CVC4_CONFIG_FILE_ONLY_IF_CHANGED(FILE)
# --------------------------------------
# Run AC_CONFIG_FILES to generate file named in the argument, but if it
# exists already, only replace it if it would be changed (this preserves
# the old timestamp if no textual changes are to be made to the file).
AC_DEFUN([CVC4_CONFIG_FILE_ONLY_IF_CHANGED], [
AC_CONFIG_FILES([$1.tmp:$1.in],
                CVC4_COPY_IF_CHANGED([$1.tmp],[$1]))
])# CVC4_CONFIG_FILE_ONLY_IF_CHANGED

# CVC4_CXX_OPTION(OPTION, VAR)
# ----------------------------
# Run $(CXX) $(CPPFLAGS) $(CXXFLAGS) OPTION and see if the compiler
# likes it.  If so, add OPTION to shellvar VAR.
AC_DEFUN([CVC4_CXX_OPTION], [
AC_MSG_CHECKING([whether $CXX supports $1])
cvc4_save_CXXFLAGS="$CXXFLAGS"
CXXFLAGS="$CXXFLAGS $WERROR $1"
AC_LANG_PUSH([C++])
AC_COMPILE_IFELSE([AC_LANG_SOURCE([int main() { return 0; }])],
                  [AC_MSG_RESULT([yes]); $2='$1'],
                  [AC_MSG_RESULT([no])])
AC_LANG_POP([C++])
CXXFLAGS="$cvc4_save_CXXFLAGS"
])# CVC4_CXX_OPTION

# CVC4_C_OPTION(OPTION, VAR)
# --------------------------
# Run $(CC) $(CPPFLAGS) $(CFLAGS) OPTION and see if the compiler
# likes it.  If so, add OPTION to shellvar VAR.
AC_DEFUN([CVC4_C_OPTION], [
AC_MSG_CHECKING([whether $CC supports $1])
cvc4_save_CFLAGS="$CFLAGS"
CFLAGS="$CFLAGS $C_WERROR $1"
AC_LANG_PUSH([C])
AC_COMPILE_IFELSE([AC_LANG_SOURCE([int main() { return 0; }])],
                  [AC_MSG_RESULT([yes]); $2='$1'],
                  [AC_MSG_RESULT([no])])
AC_LANG_POP([C])
CFLAGS="$cvc4_save_CFLAGS"
])# CVC4_C_OPTION
