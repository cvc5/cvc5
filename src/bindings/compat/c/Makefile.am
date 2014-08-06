# LIBCVC4BINDINGS_VERSION (-version-info) is in the form current:revision:age
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
LIBCVC4BINDINGS_VERSION = @CVC4_BINDINGS_LIBRARY_VERSION@

AM_CPPFLAGS = \
	-D__BUILDING_CVC4BINDINGSLIB \
	-I@builddir@/../../.. -I@srcdir@/../../../include -I@srcdir@/../../..
AM_CXXFLAGS = -Wall -Wno-return-type

lib_LTLIBRARIES =

if CVC4_LANGUAGE_BINDING_C

lib_LTLIBRARIES += libcvc4bindings_c_compat.la
libcvc4bindings_c_compat_la_LDFLAGS = \
	-version-info $(LIBCVC4BINDINGS_VERSION)
libcvc4bindings_c_compat_la_LIBADD = \
	@builddir@/../../../compat/libcvc4compat.la \
	@builddir@/../../../libcvc4.la

endif

libcvc4bindings_c_compat_la_SOURCES = \
	c_interface_defs.h \
	c_interface.h \
	c_interface.cpp
