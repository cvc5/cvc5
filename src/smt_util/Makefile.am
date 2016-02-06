AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/.. -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libsmtutil.la

libsmtutil_la_SOURCES = \
	Makefile.am \
	Makefile.in \
	boolean_simplification.cpp \
	boolean_simplification.h \
	lemma_channels.cpp \
	lemma_channels.h \
	lemma_input_channel.h \
	lemma_output_channel.h \
	nary_builder.cpp \
	nary_builder.h \
	node_visitor.h

