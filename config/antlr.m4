##
# Check for ANTLR's antlr3 script.
# Will set ANTLR to the location of the script.
##
AC_DEFUN([AC_PROG_ANTLR], [
  AC_ARG_VAR([ANTLR],[location of the antlr3 script])

  # Check the existence of the runantlr script
  if test "x$ANTLR" = "x"; then
    AC_PATH_PROG(ANTLR, [antlr3])
  else
    AC_MSG_CHECKING([antlr3 script ($ANTLR)])
    if test ! -e "$ANTLR"; then
      AC_MSG_RESULT([not found])
      unset ANTLR
    elif test ! -x "$ANTLR"; then
      AC_MSG_RESULT([not executable])
      unset ANTLR
    else
      AC_MSG_RESULT([OK])
    fi
  fi
  if test "x$ANTLR" = "x"; then
    AC_MSG_WARN(
[No usable antlr3 script found. Make sure that the parser code has
been generated already. To obtain ANTLR see <http://www.antlr3.org/>.]
    )
    ANTLR_VERSION=
  else
    ANTLR_VERSION="`$ANTLR -version 2>&1 | sed 's,.*Version  *\([[0-9.]]*\).*,\1,'`"
    case "$ANTLR_VERSION" in
      3.2|3.2.*) ANTLR_VERSION=3.2 ;;
      3.4|3.4.*) ANTLR_VERSION=3.4 ;;
      *) AC_MSG_WARN([unknown version of antlr: $ANTLR_VERSION]);;
    esac
  fi
])

##
# Check the existence of the ANTLR3 C runtime library and headers
# Will set ANTLR_INCLUDES and ANTLR_LIBS to the location of the ANTLR
# headers and library respectively
##
AC_DEFUN([AC_LIB_ANTLR],[
  AC_ARG_VAR(ANTLR_HOME, [path to libantlr3c installation])

  # Get the location of the ANTLR3 C includes and libraries
  AC_ARG_WITH(
    [antlr-dir],
    AS_HELP_STRING(
      [--with-antlr-dir=PATH],
      [path to ANTLR C headers and libraries]
    ),
    ANTLR_PREFIXES="$withval",
    ANTLR_PREFIXES="$ANTLR_HOME /usr/local /usr /opt/local /opt"
  )

  AC_MSG_CHECKING(for ANTLR3 C runtime library)

  # Use C and remember the variables we are changing
  AC_LANG_PUSH(C)
  OLD_CPPFLAGS="$CPPFLAGS"
  OLD_LIBS="$LIBS"

  # Try all the includes/libs set in ANTLR_PREFIXES
  for antlr_prefix in $ANTLR_PREFIXES
  do
    CPPFLAGS="$OLD_CPPFLAGS -I$antlr_prefix/include"
    LIBS="$OLD_LIBS -L$antlr_prefix/lib -lantlr3c"
    AC_LINK_IFELSE([AC_LANG_SOURCE(
      [
        #include <antlr3.h>

        int main() {
          pANTLR3_TOKEN_FACTORY factory = antlr3TokenFactoryNew((pANTLR3_INPUT_STREAM) NULL);
          return 0;
        }
      ])],
      [
        AC_MSG_RESULT(found in $antlr_prefix)
        ANTLR_INCLUDES="-I$antlr_prefix/include"
        ANTLR_LDFLAGS="-L$antlr_prefix/lib -lantlr3c"
        break
      ],
          [
            AC_MSG_RESULT(no)
            AC_MSG_ERROR([ANTLR3 C runtime not found, see <http://www.antlr3.org/>])
          ]
    )
  done

  AC_MSG_CHECKING([for presence of older antlr3AsciiFileStreamNew()])
  AC_LINK_IFELSE([AC_LANG_SOURCE(
    [
      #include <antlr3.h>

      int main() {
        pANTLR3_UINT8 fName = (pANTLR3_UINT8)"foo";
        pANTLR3_INPUT_STREAM input = antlr3AsciiFileStreamNew(fName);
        return 0;
      }
    ])],
    [
      AC_MSG_RESULT([found it (must be antlr3 3.2 or similar)])
      if test -n "$ANTLR_VERSION" -a "$ANTLR_VERSION" != 3.2; then
        AC_MSG_WARN([your antlr parser generator is version $ANTLR_VERSION, which doesn't match the library!])
      fi
      CVC4CPPFLAGS="${CVC4CPPFLAGS:+$CVC4CPPFLAGS }-DCVC4_ANTLR3_OLD_INPUT_STREAM"
    ],
        [
          AC_MSG_RESULT(failed)
          AC_MSG_CHECKING([for presence of newer antlr3FileStreamNew()])
          AC_LINK_IFELSE([AC_LANG_SOURCE(
            [
              #include <antlr3.h>

              int main() {
                pANTLR3_UINT8 fName = (pANTLR3_UINT8)"foo";
                pANTLR3_INPUT_STREAM input = antlr3FileStreamNew(fName, ANTLR3_ENC_8BIT);
                return 0;
              }
            ])],
            [
              AC_MSG_RESULT([found it (must be antlr3 3.4 or similar)])
              if test -n "$ANTLR_VERSION" -a "$ANTLR_VERSION" != 3.4; then
                AC_MSG_WARN([your antlr parser generator is version $ANTLR_VERSION, which doesn't match the library!])
              fi
            ],
                [
                  AC_MSG_ERROR([cannot figure out how to create an antlr3 input stream, bailing..])
                ]
          )
        ]
  )

  # Return the old compile variables and pop the language.
  LIBS="$OLD_LIBS"
  CPPFLAGS="$OLD_CPPFLAGS"
  AC_LANG_POP()

  # Define the ANTLR include/libs variables
  AC_SUBST(ANTLR_INCLUDES)
  AC_SUBST(ANTLR_LDFLAGS)
])
