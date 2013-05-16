# CVC4_SUPPORTED_BINDINGS
# -----------------------
# Supported language bindings for CVC4.
AC_DEFUN([CVC4_SUPPORTED_BINDINGS],
[c,c++,java])

# CVC4_ALL_BINDINGS
# -----------------
# All language bindings for CVC4 (may include unofficial bindings).
AC_DEFUN([CVC4_ALL_BINDINGS],
[c,java,csharp,perl,php,python,ruby,tcl,ocaml])

# CVC4_NEED_SWIG_FOR_BINDING
# --------------------------
# Used by CVC4_CHECK_BINDINGS to ensure swig is available (and correct
# version) when a binding needs it
AC_DEFUN([CVC4_NEED_SWIG_FOR_BINDING], [
  if test -z "$SWIG"; then
    AC_MSG_WARN([swig not available or incompatible version; $binding bindings require swig 2.0.0 or later])
    binding_error=yes
  fi
])

# CVC4_CHECK_BINDINGS(DEFAULT_BINDINGS_LIST)
# ------------------------------------------
# Check for user language binding preferences, and what is possible
# to build on the build host.
AC_DEFUN([CVC4_CHECK_BINDINGS], [
dnl Check for SWIG (for building language bindings)
noswig=no

m4_foreach(lang,[CVC4_ALL_BINDINGS],
[[cvc4_build_]]lang[[_bindings=no
]])

AC_ARG_VAR(SWIG, [SWIG binary (used to generate language bindings)])
AC_ARG_WITH([swig],
  [AS_HELP_STRING([--with-swig=BINARY], [path to swig binary])],
  [if test "$withval" = no; then noswig=yes; else SWIG="$withval"; fi])
AC_ARG_ENABLE([language-bindings],
  [AS_HELP_STRING([--enable-language-bindings=][CVC4_SUPPORTED_BINDINGS][ | all], [specify language bindings to build])],
  [if test "$enableval" = yes; then cvc4_check_for_bindings=yes; try_bindings='$1'; else cvc4_check_for_bindings=no; if test "$enableval" = no; then try_bindings=; else try_bindings="$enableval"; fi; fi],
  [cvc4_check_for_bindings=no; try_bindings=])
CVC4_LANGUAGE_BINDINGS=
if test "$noswig" = yes; then
  AC_MSG_WARN([use of swig disabled by user, native API bindings disabled.])
  SWIG=
else
  if test -z "$SWIG"; then
    AC_CHECK_PROGS(SWIG, [swig swig2.0], [], [])
  else
    AC_CHECK_PROG(SWIG, "$SWIG", "$SWIG", [])
  fi
  if test -z "$SWIG"; then
    AC_MSG_RESULT([not found])
    AC_MSG_WARN([language bindings for native API disabled, swig not found.])
  else
    AC_MSG_CHECKING([compatibility with version of swig])
    cat > conftest.c << _CVC4EOF
%module conftest
#if !defined(SWIG_VERSION) || SWIG_VERSION < 0x020000
#error bad version
#endif
_CVC4EOF
    if $SWIG conftest.c >&AS_MESSAGE_LOG_FD 2>&1; then
      AC_MSG_RESULT([compatible version])
    else
      AC_MSG_RESULT([incompatible version])
      AC_MSG_WARN([swig version 2.0.0 or later is required to build native API bindings])
      SWIG=
      echo '===Failed swig input was:' >&AS_MESSAGE_LOG_FD
      cat conftest.c >&AS_MESSAGE_LOG_FD
      echo '===End failed swig input' >&AS_MESSAGE_LOG_FD
      rm -f conftest.c
    fi
  fi
fi

AC_MSG_CHECKING([for requested user language bindings])
if test "$try_bindings" = all; then
  try_bindings='CVC4_SUPPORTED_BINDINGS'
fi
try_bindings=$(echo "$try_bindings" | sed 's/,/ /g')
if test -z "$try_bindings"; then
  AC_MSG_RESULT([none])
else
  AC_MSG_RESULT([$try_bindings])
fi
CVC4_UNSUPPORTED_LANGUAGE_BINDINGS=
cvc4_save_CPPFLAGS="$CPPFLAGS"
cvc4_save_CXXFLAGS="$CXXFLAGS"
AC_LANG_PUSH([C++])
for binding in $try_bindings; do
  __cvc4_lang_supported=no
  m4_foreach([__cvc4_supported_binding], [CVC4_SUPPORTED_BINDINGS],
    [if test "$binding" = "__cvc4_supported_binding"; then __cvc4_lang_supported=yes; fi
  ])dnl
  if test $__cvc4_lang_supported = no; then
    CVC4_UNSUPPORTED_LANGUAGE_BINDINGS="${CVC4_UNSUPPORTED_LANGUAGE_BINDINGS:+$CVC4_UNSUPPORTED_LANGUAGE_BINDINGS }$binding"
  fi

  binding_error=no
  AC_MSG_CHECKING([for availability of $binding binding])
  case "$binding" in
    c++)
      AC_MSG_RESULT([C++ is built by default]);;
    c)
      cvc4_build_c_bindings=yes
      AC_MSG_RESULT([C support will be built]);;
    java)
      AC_MSG_RESULT([Java support will be built])
      CVC4_NEED_SWIG_FOR_BINDING
      AC_ARG_VAR(JAVA_CPPFLAGS, [flags to pass to compiler when building Java bindings])
      CPPFLAGS="$CPPFLAGS $JAVA_CPPFLAGS"
      AC_CHECK_HEADER([jni.h], [cvc4_build_java_bindings=yes], [binding_error=yes])
      ;;
    csharp)
      AC_MSG_RESULT([[C# support will be built]])
      CVC4_NEED_SWIG_FOR_BINDING
      AC_ARG_VAR(CSHARP_CPPFLAGS, [flags to pass to compiler when building C# bindings])
      CPPFLAGS="$CPPFLAGS $CSHARP_CPPFLAGS"
      cvc4_build_csharp_bindings=yes
      ;;
    perl)
      AC_MSG_RESULT([perl support will be built])
      CVC4_NEED_SWIG_FOR_BINDING
      AC_ARG_VAR(PERL_CPPFLAGS, [flags to pass to compiler when building perl bindings])
      CPPFLAGS="$CPPFLAGS $PERL_CPPFLAGS"
      AC_CHECK_HEADER([EXTERN.h], [cvc4_build_perl_bindings=yes], [binding_error=yes])
      ;;
    php)
      AC_MSG_RESULT([php support will be built])
      CVC4_NEED_SWIG_FOR_BINDING
      AC_ARG_VAR(PHP_CPPFLAGS, [flags to pass to compiler when building PHP bindings])
      CPPFLAGS="$CPPFLAGS $PHP_CPPFLAGS"
      AC_CHECK_HEADER([zend.h], [cvc4_build_php_bindings=yes], [binding_error=yes])
      ;;
    python)
      AC_MSG_RESULT([python support will be built])
      CVC4_NEED_SWIG_FOR_BINDING
      AM_PATH_PYTHON([2.5], [cvc4_build_python_bindings=yes], [binding_error=yes])
      AC_ARG_VAR([PYTHON_INCLUDE], [Include flags for python, bypassing python-config])
      AC_ARG_VAR([PYTHON_CONFIG], [Path to python-config])
      AS_IF([test -z "$PYTHON_INCLUDE"], [
        AS_IF([test -z "$PYTHON_CONFIG"], [
          AC_PATH_PROGS([PYTHON_CONFIG],
            [python$PYTHON_VERSION-config python-config],
            [no]
          )
          AS_IF([test "$PYTHON_CONFIG" = no], [AC_MSG_ERROR([cannot find python-config for $PYTHON.])])
         ])
        AC_MSG_CHECKING([python include flags])
        AC_SUBST(PYTHON_CXXFLAGS, `$PYTHON_CONFIG --includes`)
        AC_MSG_RESULT([$PYTHON_CXXFLAGS])
      ])
      CPPFLAGS="$CPPFLAGS $PYTHON_CXXFLAGS"
      AC_CHECK_HEADER([Python.h], [cvc4_build_python_bindings=yes], [binding_error=yes])     
      ;;
    ruby)
      AC_MSG_RESULT([ruby support will be built])
      CVC4_NEED_SWIG_FOR_BINDING
      AC_ARG_VAR(RUBY_CPPFLAGS, [flags to pass to compiler when building ruby bindings])
      CPPFLAGS="$CPPFLAGS $RUBY_CPPFLAGS"
      AC_CHECK_HEADER([ruby.h], [cvc4_build_ruby_bindings=yes], [binding_error=yes])
      ;;
    tcl)
      AC_MSG_RESULT([tcl support will be built])
      CVC4_NEED_SWIG_FOR_BINDING
      AC_ARG_VAR(TCL_CPPFLAGS, [flags to pass to compiler when building tcl bindings])
      CPPFLAGS="$CPPFLAGS $TCL_CPPFLAGS"
      AC_CHECK_HEADER([tcl.h], [cvc4_build_tcl_bindings=yes], [binding_error=yes])
      ;;
    ocaml)
      AC_MSG_RESULT([OCaml support will be built])
      CVC4_NEED_SWIG_FOR_BINDING
      AC_ARG_VAR(TCL_CPPFLAGS, [flags to pass to compiler when building OCaml bindings])
      CPPFLAGS="$CPPFLAGS $OCAML_CPPFLAGS"
      AC_CHECK_HEADER([caml/misc.h], [cvc4_build_ocaml_bindings=yes], [binding_error=yes])
      if test "$binding_error" = no; then
        AC_ARG_VAR(OCAMLC, [OCaml compiler])
        if test -z "$OCAMLC"; then
          AC_CHECK_PROGS(OCAMLC, ocamlc, ocamlc, [])
        else
          AC_CHECK_PROG(OCAMLC, "$OCAMLC", "$OCAMLC", [])
        fi
        AC_ARG_VAR(OCAMLMKTOP, [OCaml runtime-maker])
        if test -z "$OCAMLMKTOP"; then
          AC_CHECK_PROGS(OCAMLMKTOP, ocamlmktop, ocamlmktop, [])
        else
          AC_CHECK_PROG(OCAMLMKTOP, "$OCAMLMKTOP", "$OCAMLMKTOP", [])
        fi
        AC_ARG_VAR(OCAMLFIND, [OCaml-find binary])
        if test -z "$OCAMLFIND"; then
          AC_CHECK_PROGS(OCAMLFIND, ocamlfind, ocamlfind, [])
        else
          AC_CHECK_PROG(OCAMLFIND, "$OCAMLFIND", "$OCAMLFIND", [])
        fi
        AC_ARG_VAR(CAMLP4O, [camlp4o binary])
        if test -z "$CAMLP4O"; then
          AC_CHECK_PROGS(CAMLP4O, camlp4o, camlp4o, [])
        else
          AC_CHECK_PROG(CAMLP4O, "$CAMLP4O", "$CAMLP4O", [])
        fi
      fi
      ;;
    *) AC_MSG_RESULT([unknown binding]); binding_error=yes;;
  esac
  if test "$binding_error" = yes; then
    if test "$cvc4_check_for_bindings" = no; then
      AC_MSG_ERROR([Language binding \`$binding' requested by user, but it cannot be built (the preceding few lines should give an indication why this is).])
    else
      AC_MSG_WARN([Language binding \`$binding' cannot be built (the preceding few lines should give an indication why this is).])
    fi
  else
    CVC4_LANGUAGE_BINDINGS="${CVC4_LANGUAGE_BINDINGS:+$CVC4_LANGUAGE_BINDINGS }$binding"
  fi
  AC_LANG_POP([C++])
  CXXFLAGS="$cvc4_save_CXXFLAGS"
  CPPFLAGS="$cvc4_save_CPPFLAGS"
done

AM_CONDITIONAL([CVC4_HAS_SWIG], [test "$SWIG"])

m4_foreach([lang], [CVC4_ALL_BINDINGS],
[AM_CONDITIONAL([CVC4_LANGUAGE_BINDING_]m4_toupper(lang), [test "$cvc4_build_]lang[_bindings" = yes])
])dnl

AC_SUBST(SWIG)
AC_SUBST(CVC4_LANGUAGE_BINDINGS)

])# CVC4_CHECK_BINDINGS
