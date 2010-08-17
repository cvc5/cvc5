AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../../include -I@srcdir@/../../.. -I@builddir@/../../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libufmorgan.la

libufmorgan_la_SOURCES = \
	theory_uf_morgan.h \
	theory_uf_morgan.cpp

EXTRA_DIST =
