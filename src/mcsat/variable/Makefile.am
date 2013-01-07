AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-D __STDC_LIMIT_MACROS \
	-D __STDC_FORMAT_MACROS \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../.. 
AM_CXXFLAGS = -Wall -Wno-parentheses -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libmcsat_variable.la

libmcsat_variable_la_SOURCES = \
	variable.h \
	variable.cpp \
	variable_db.h \
	variable_db.cpp \
	variable_table.h
	
EXTRA_DIST = 

SUBDIRS = 

