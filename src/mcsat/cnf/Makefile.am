AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-D __STDC_LIMIT_MACROS \
	-D __STDC_FORMAT_MACROS \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../.. 
AM_CXXFLAGS = -Wall -Wno-parentheses -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libmcsat_cnf.la

libmcsat_cnf_la_SOURCES = \
	cnf_stream.h \
	cnf_stream.cpp \
	tseitin_cnf_stream.h \
	tseitin_cnf_stream.cpp \
	cnf_plugin.h \
	cnf_plugin.cpp
	
EXTRA_DIST = 

SUBDIRS = 

