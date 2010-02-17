AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../..
AM_CXXFLAGS = -Wall -fvisibility=hidden

noinst_LTLIBRARIES = libuf.la

libuf_la_SOURCES = \
	ecdata.h \
	ecdata.cpp \
	theory_uf.h \
	theory_uf.cpp

EXTRA_DIST = kinds
