AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

if CVC4_NEEDS_REPLACEMENT_FUNCTIONS
noinst_LTLIBRARIES = libreplacements.la
endif

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
