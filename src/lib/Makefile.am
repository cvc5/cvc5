AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/.. -I@srcdir@/../include -I@srcdir@/..
AM_CFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)
# This is a workaround for now to fix some warnings related to unsupported
# compiler flags since we are compiling C code here. CXXFLAGS is set via
# configure, however, we should actually set AM_CXXFLAGS.
CXXFLAGS = $(AM_CXXFLAGS)

noinst_LTLIBRARIES = libreplacements.la

libreplacements_la_SOURCES =

libreplacements_la_LIBADD = \
	$(LTLIBOBJS)

EXTRA_DIST = \
	replacements.h \
	clock_gettime.c \
	clock_gettime.h \
	strtok_r.c \
	strtok_r.h \
	ffs.c \
	ffs.h
