AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libreplacements.la

libreplacements_la_SOURCES = empty.c
libreplacements_la_LIBADD = \
	$(LTLIBOBJS)

EXTRA_DIST = \
	replacements.h \
	clock_gettime.c \
	clock_gettime.h

CLEANFILES = empty.c

# empty.c hack -- need *some* source file so that library make rules are built
empty.c:; touch empty.c
