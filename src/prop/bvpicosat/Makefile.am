AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-D __STDC_LIMIT_MACROS \
	-D __STDC_FORMAT_MACROS \
	-I@srcdir@/ -I@srcdir@/../.. -I@srcdir@/../../.. -I@builddir@/../../.. -I@srcdir@/../../../include
AM_CXXFLAGS = -Wall -Wno-parentheses -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libpicosat.la
libpicosat_la_SOURCES = \
	app.c \
	picosat.h \
	picosat.c \
	picomus.c \
	version.c

EXTRA_DIST = \
	main.c \
	README \
	LICENSE \
	NEWS \
	VERSION \
	configure \
	mkconfig \
	makefile.in
