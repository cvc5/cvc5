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
	command.cpp \
	command.h \
	dump.h \
	dump.cpp \
	lemma_input_channel.h \
	lemma_output_channel.h \
	ite_removal.cpp \
	ite_removal.h \
	model.cpp \
	model.h \
	nary_builder.cpp \
	nary_builder.h \
	node_visitor.h


EXTRA_DIST = \
	command.i

