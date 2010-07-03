AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libcontext.la

libcontext_la_SOURCES = \
	context.cpp \
	context.h \
	context_mm.cpp \
	context_mm.h \
	cdo.h \
	cdlist.h \
	cdmap.h \
	cdset.h
