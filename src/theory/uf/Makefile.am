AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libuf.la

libuf_la_SOURCES = \
	ecdata.h \
	ecdata.cpp \
	theory_uf.h \
	theory_uf.cpp \
	theory_uf_type_rules.h 

EXTRA_DIST = kinds
