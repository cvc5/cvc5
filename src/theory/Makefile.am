AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -fvisibility=hidden

noinst_LTLIBRARIES = libtheory.la

libtheory_la_SOURCES = \
	theory_engine.h \
	theory_engine.cpp \
	theory.h \
	theory.cpp

libtheory_la_LIBADD = \
	@builddir@/uf/libuf.la

SUBDIRS = uf
