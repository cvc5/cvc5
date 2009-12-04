##
# Check for ANTLR's runantlr script. Will set ANTLR to the location of the
# runantlr script  
##
AC_DEFUN([AC_PROG_ANTLR], [
  
  # Get the location of the runantlr script
  AC_ARG_WITH(
    [antlr],
    AC_HELP_STRING(
      [--with-antlr=RUNANTLR],
      [location of the ANTLR's `runantlr` script]      
    ),
    ANTLR="$withval",
    ANTLR="runantlr"     
  )  

  # Check the existance of the runantlr script
  AC_CHECK_PROG(ANTLR, "$ANTLR", "$ANTLR", [])
  if test no$ANTLR = "no"; 
  then
    AC_MSG_WARN(
      [Couldn't find the runantlr script, make sure that the parser code has 
      been generated already. To obtain ANTLR see <http://www.antlr.org/>.]
    )
    AC_MSG_RESULT(no)
  fi  

  # Define the ANTL related variables   
  AC_SUBST(ANTLR)  
])

##
# Check the existnace of the ANTLR C++ runtime library and headers
# Will set ANTLR_CPPFLAGS and ANTLR_LIBS to the location of the ANTLR headers
# and library respectively
##
AC_DEFUN([AC_LIB_ANTLR],[

  # Get the location of the  ANTLR c++ includes and libraries
  AC_ARG_WITH(
    [antlr-prefix],
    AC_HELP_STRING(
      [--with-antlr-prefix=PATH],
      [set the search path for ANTLR headers and libraries to `PATH/include`
       and `PATH/lib`. By default we look in /usr, /usr/local, /opt and 
       /opt/local.
      ]
    ),
    ANTLR_PREFIXES="$withval",
    ANTLR_PREFIXES="/usr/local /usr /opt/local /opt"
  )

  AC_MSG_CHECKING(for antlr C++ runtime library)

  # Use C++ and remember the variables we are changing 
  AC_LANG_PUSH(C++)
  OLD_CPPFLAGS="$CPPFLAGS"
  OLD_LIBS="$LIBS"
  
  # Try all the includes/libs set in ANTLR_PREFIXES
  for antlr_prefix in $ANTLR_PREFIXES
  do    
    CPPFLAGS="$OLD_CPPFLAGS -I$antlr_prefix/include"
    LIBS="$OLD_LIBS -L$antlr_prefix/lib -lantlr"
    AC_LINK_IFELSE(
      [
        #include <antlr/CommonAST.hpp>
        class MyAST : public ANTLR_USE_NAMESPACE(antlr)CommonAST {
        };
        int main() {
          MyAST ast;
        }
      ], 
      [
        AC_MSG_RESULT(found in $antlr_prefix)
        ANTLR_INCLUDES="-I$antlr_prefix/include"
        ANTLR_LDFLAGS="-L$antlr_prefix/lib -lantlr-pic"
        break
      ], 
      [
        AC_MSG_RESULT(no)
        AC_MSG_ERROR([ANTLR C++ runtime not found, see <http://www.antlr.org/>])
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
