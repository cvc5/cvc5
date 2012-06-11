AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libarrays.la

libarrays_la_SOURCES = \
	theory_arrays_type_rules.h \
	theory_arrays_rewriter.h \
	theory_arrays.h \
	theory_arrays.cpp \
	union_find.h \
	union_find.cpp \
	array_info.h \
	array_info.cpp \
	static_fact_manager.h \
	static_fact_manager.cpp \
	theory_arrays_instantiator.h \
	theory_arrays_instantiator.cpp

EXTRA_DIST = kinds
