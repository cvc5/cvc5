# CVC4_SUPPORTED_BINDINGS
# -----------------------
# Supported language bindings for CVC4.
AC_DEFUN([CVC4_SUPPORTED_BINDINGS],
[java,csharp,perl,php,python,ruby,tcl,ocaml])

# CVC4_CHECK_BINDINGS(DEFAULT_BINDINGS_LIST)
# ------------------------------------------
# Check for user language binding preferences, and what is possible
# to build on the build host.
AC_DEFUN([CVC4_CHECK_BINDINGS], [
dnl Check for SWIG (for building language bindings)
noswig=no

m4_foreach(lang,[CVC4_SUPPORTED_BINDINGS],
[[cvc4_build_]]lang[[_bindings=no
]])

AC_ARG_VAR(SWIG, [SWIG binary (used to generate language bindings)])
AC_ARG_WITH([swig],
  [AS_HELP_STRING([--with-swig=BINARY], [path to swig binary])],
  [if test "$withval" = no; then noswig=yes; else SWIG="$withval"; fi])
AC_ARG_ENABLE([language-bindings],
  [AS_HELP_STRING([--enable-language-bindings=][CVC4_SUPPORTED_BINDINGS], [specify language bindings to build])],
  [cvc4_check_for_bindings=no; if test "$enableval" = no; then try_bindings=; else try_bindings="$enableval"; fi],
  [cvc4_check_for_bindings=yes; try_bindings=])
CVC4_LANGUAGE_BINDINGS=
if test "$noswig" = yes; then
  AC_MSG_WARN([use of swig disabled by user.])
  SWIG=
  if test "$cvc4_check_for_bindings" = no -a -n "$try_bindings"; then
    AC_MSG_ERROR([language bindings requested by user, but swig disabled.])
  fi
else
  if test -z "$SWIG"; then
    AC_CHECK_PROGS(SWIG, swig, swig, [])
  else
    AC_CHECK_PROG(SWIG, "$SWIG", "$SWIG", [])
  fi
  if test -z "$SWIG"; then
    AC_MSG_WARN([language bindings disabled, swig not found.])
    if test "$cvc4_check_for_bindings" = no -a -n "$try_bindings"; then
      AC_MSG_ERROR([language bindings requested by user, but swig disabled.])
    fi
  else
    AC_MSG_CHECKING([for requested user language bindings])
    if test "$cvc4_check_for_bindings" = yes; then
      try_bindings='$1'
    else
      try_bindings=$(echo "$try_bindings" | sed 's/,/ /g')
    fi
    AC_MSG_RESULT([$try_bindings])
    JAVA_INCLUDES=
    for binding in $try_bindings; do
      binding_error=no
      AC_MSG_CHECKING([for availability of $binding binding])
      case "$binding" in
        c++) AC_MSG_RESULT([C++ is built by default]);;
        java)
          JAVA_INCLUDES="-I/usr/lib/jvm/java-6-sun-1.6.0.26/include -I/usr/lib/jvm/java-6-sun-1.6.0.26/include/linux"
          cvc4_build_java_bindings=yes
          AC_MSG_RESULT([Java support will be built]);;
        csharp)
          binding_error=yes
          AC_MSG_RESULT([$binding not supported yet]);;
        perl)
          binding_error=yes
          AC_MSG_RESULT([$binding not supported yet]);;
        php)
          binding_error=yes
          AC_MSG_RESULT([$binding not supported yet]);;
        python)
          binding_error=yes
          AC_MSG_RESULT([$binding not supported yet]);;
        ruby)
          binding_error=yes
          AC_MSG_RESULT([$binding not supported yet]);;
        tcl)
          binding_error=yes
          AC_MSG_RESULT([$binding not supported yet]);;
        ocaml)
          binding_error=yes
          AC_MSG_RESULT([$binding not supported yet]);;
        *) AC_MSG_RESULT([unknown binding]); binding_error=yes;;
      esac
      if test "$binding_error" = yes -a "$cvc4_check_for_bindings" = no; then
        AC_MSG_ERROR([Language binding \`$binding' requested by user, but it cannot be built.])
      fi
      CVC4_LANGUAGE_BINDINGS="${CVC4_LANGUAGE_BINDINGS:+$CVC4_LANGUAGE_BINDINGS }$binding"
    done
  fi
fi

m4_foreach([lang], [CVC4_SUPPORTED_BINDINGS],
[AM_CONDITIONAL([CVC4_LANGUAGE_BINDING_]m4_toupper(lang), [test "$cvc4_build_]lang[_bindings" = yes])
])dnl

AC_SUBST(SWIG)
AC_SUBST(JAVA_INCLUDES)
AC_SUBST(CVC4_LANGUAGE_BINDINGS)

])# CVC4_CHECK_BINDINGS
