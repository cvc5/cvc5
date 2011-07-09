AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libuf.la

# force automake to link using g++
nodist_EXTRA_libuf_la_SOURCES = \
	dummy.cpp

libuf_la_SOURCES = \
	theory_uf.h \
	theory_uf.cpp \
	theory_uf_type_rules.h \
	theory_uf_rewriter.h \
	equality_engine.h \
	equality_engine_impl.h

libuf_la_LIBADD = \
	@builddir@/tim/libuftim.la \
	@builddir@/morgan/libufmorgan.la

SUBDIRS = tim morgan

EXTRA_DIST = kinds
