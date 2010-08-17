AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../../include -I@srcdir@/../../.. -I@builddir@/../../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libuftim.la

libuftim_la_SOURCES = \
	ecdata.h \
	ecdata.cpp \
	theory_uf_tim.h \
	theory_uf_tim.cpp

EXTRA_DIST =
