# CHECK_FOR_IS_SORTED
# -------------------
# Look for is_sorted in std:: and __gnu_cxx:: and define
# some things to make it easy to find later.
AC_DEFUN([CHECK_FOR_IS_SORTED], [
AC_MSG_CHECKING([where we can find is_sorted])
AC_LANG_PUSH([C++])
is_sorted_result=
AC_COMPILE_IFELSE([AC_LANG_PROGRAM([#include <algorithm>],
                                   [std::is_sorted((int*)0L, (int*)0L);])],
  [is_sorted_result=std],
  [AC_COMPILE_IFELSE([AC_LANG_PROGRAM([#include <ext/algorithm>],
                                      [__gnu_cxx::is_sorted((int*)0L, (int*)0L);])],
    [is_sorted_result=__gnu_cxx],
    [AC_MSG_FAILURE([cannot find std::is_sorted() or __gnu_cxx::is_sorted()])])])
AC_LANG_POP([C++])
AC_MSG_RESULT($is_sorted_result)
if test "$is_sorted_result" = __gnu_cxx; then is_sorted_result=1; else is_sorted_result=0; fi
AC_DEFINE_UNQUOTED([IS_SORTED_IN_GNUCXX_NAMESPACE], $is_sorted_result, [Define to 1 if __gnu_cxx::is_sorted() exists])
])# CHECK_FOR_IS_SORTED
