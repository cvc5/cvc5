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

unset ac_cvc4_rewritten_args
for ac_option
do
  case $ac_option in
    -*|*=*) ;;
    production|production-*|debug|debug-*|default|default-*|competition|competition-*)
      # regexp `\?' not supported on Mac OS X
      ac_option_build=`expr "$ac_option" : '\([[^-]]*\)-\{0,1\}'`
      ac_cvc4_build_profile_set=yes
      AC_MSG_NOTICE([CVC4: building profile $ac_option_build])
      for x in optimized statistics assertions tracing muzzle coverage profiling; do
        if expr "$ac_option" : '.*-no'$x'-\{0,1\}$' >/dev/null; then
          eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--disable-$x\""'
        fi
        if expr "$ac_option" : '.*-'$x'-\{0,1\}$' >/dev/null; then
          eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--enable-$x\""'
        fi
      done
      if expr "$ac_option" : '.*-nostaticbinary-\{0,1\}$' >/dev/null; then
        eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--disable-static-binary\""'
      fi
      if expr "$ac_option" : '.*-staticbinary-\{0,1\}$' >/dev/null; then
        eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--enable-static-binary\""'
      fi
      if expr "$ac_option" : '.*-nodebugsymbols-\{0,1\}$' >/dev/null; then
        eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--disable-debug-symbols\""'
      fi
      if expr "$ac_option" : '.*-debugsymbols-\{0,1\}$' >/dev/null; then
        eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--enable-debug-symbols\""'
      fi
      for x in cln gmp; do
        if expr "$ac_option" : '.*-no'$x'-\{0,1\}$' >/dev/null; then
          eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--without-$x\""'
        fi
        if expr "$ac_option" : '.*-'$x'-\{0,1\}$' >/dev/null; then
          eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"--with-$x\""'
        fi
      done
      ac_option="--with-build=$ac_option_build"
  esac
  eval 'ac_cvc4_rewritten_args="${ac_cvc4_rewritten_args+$ac_cvc4_rewritten_args }\"$ac_option\""'
done
eval set x $ac_cvc4_rewritten_args
shift
dnl echo "args are now:" "${@}"
m4_divert_pop([PARSE_ARGS])dnl
])# CVC4_REWRITE_ARGS_FOR_BUILD_PROFILE
