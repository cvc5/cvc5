##
# Check for ANTLR's antlr3 script.
# Will set ANTLR to the location of the script.
##
AC_DEFUN([AC_PROG_ANTLR], [
  AC_ARG_VAR([ANTLR],[location of the antlr3 script])

  # Check the existence of the runantlr script
  if test -z "$ANTLR"; then
    AC_CHECK_PROGS(ANTLR, [antlr3])
  else
    AC_CHECK_PROG(ANTLR, "$ANTLR", "$ANTLR", [])
  fi
  if test no$ANTLR = "no";
  then
    AC_MSG_WARN(
      [Couldn't find the antlr3 script, make sure that the parser code has
      been generated already. To obtain ANTLR see <http://www.antlr.org/>.]
    )
    AC_MSG_RESULT(no)
  fi

  # Define the ANTL related variables
  # AC_SUBST(ANTLR)
])

##
# Check the existence of the ANTLR3 C runtime library and headers
# Will set ANTLR_INCLUDES and ANTLR_LIBS to the location of the ANTLR headers
# and library respectively
##
AC_DEFUN([AC_LIB_ANTLR],[

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
    AC_LINK_IFELSE(
      [
        #include <antlr3.h>

        int main() {
          pANTLR3_UINT8 fName = (pANTLR3_UINT8)"foo";
          pANTLR3_INPUT_STREAM input = antlr3AsciiFileStreamNew(fName);
          return 0;
        }
      ],
      [
        AC_MSG_RESULT(found in $antlr_prefix)
        ANTLR_INCLUDES="-I$antlr_prefix/include"
        ANTLR_LDFLAGS="-L$antlr_prefix/lib -lantlr3c"
        break
      ],
          [
            AC_MSG_RESULT(no)
            AC_MSG_ERROR([ANTLR3 C runtime not found, see <http://www.antlr.org/>])
          ]
    )
  done

  # Return the old compile variables and pop the language.
  LIBS="$OLD_LIBS"
  CPPFLAGS="$OLD_CPPFLAGS"
  AC_LANG_POP()

  # Define the ANTLR include/libs variables
  AC_SUBST(ANTLR_INCLUDES)
  AC_SUBST(ANTLR_LDFLAGS)
])
