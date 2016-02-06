AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/.. -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libbase.la

# Do not list built sources (like tls.h) here!
# Rather, list them under BUILT_SOURCES, and their .in versions under
# EXTRA_DIST.  Otherwise, they're packaged up in the tarball, which is
# no good---they belong in the configured builds/ directory.  If they
# end up in the source directory, they build the cvc4 that was
# configured at the time of the "make dist", which (1) may not be the
# configuration that the user wants, and (2) might cause link errors.
libbase_la_SOURCES = \
	Makefile.am \
	Makefile.in \
	cvc4_assert.cpp \
	cvc4_assert.h \
	exception.cpp \
	exception.h \
	listener.cpp \
	listener.h \
	modal_exception.h \
	output.cpp \
	output.h



BUILT_SOURCES = \
	tls.h

EXTRA_DIST = \
	exception.i \
	modal_exception.i \
	tls.h.in

DISTCLEANFILES = \
	tls.h.tmp \
	tls.h
