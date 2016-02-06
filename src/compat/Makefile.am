# LIBCVC4COMPAT_VERSION (-version-info) is in the form current:revision:age
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
LIBCVC4COMPAT_VERSION = @CVC4_COMPAT_LIBRARY_VERSION@

AM_CPPFLAGS = \
	-D__BUILDING_CVC4COMPATLIB \
	-I@builddir@/.. $(ANTLR_INCLUDES) -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas

if CVC4_BUILD_LIBCOMPAT

lib_LTLIBRARIES = libcvc4compat.la

libcvc4compat_la_LDFLAGS = \
	-version-info $(LIBCVC4COMPAT_VERSION)

libcvc4compat_la_LIBADD = \
	@builddir@/../libcvc4.la \
	@builddir@/../parser/libcvc4parser.la \
	@builddir@/../lib/libreplacements.la

libcvc4compat_la_SOURCES = \
	cvc3_compat.h \
	cvc3_compat.cpp
libcvc4compat_la_CXXFLAGS = -fno-strict-aliasing

else

EXTRA_DIST = \
	cvc3_kinds.h \
	cvc3_compat.h \
	cvc3_compat.cpp

endif
