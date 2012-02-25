AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-D __STDC_LIMIT_MACROS \
	-D __STDC_FORMAT_MACROS \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/.. -I@srcdir@/minisat -I@srcdir@/bvminisat
AM_CXXFLAGS = -Wall -Wno-parentheses -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libprop.la

libprop_la_SOURCES = \
	registrar.h \
	prop_engine.cpp \
	prop_engine.h \
	sat.h \
	sat.cpp \
	cnf_stream.h \
	cnf_stream.cpp \
	sat_module.h \
	sat_module.cpp

SUBDIRS = minisat bvminisat

