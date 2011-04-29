AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libdatatypes.la

libdatatypes_la_SOURCES = \
	theory_datatypes_type_rules.h \
	theory_datatypes.h \
	datatypes_rewriter.h \
	theory_datatypes.cpp \
	union_find.h \
	union_find.cpp \
	explanation_manager.h \
	explanation_manager.cpp

EXTRA_DIST = kinds
