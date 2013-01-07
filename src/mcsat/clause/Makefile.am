AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-D __STDC_LIMIT_MACROS \
	-D __STDC_FORMAT_MACROS \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../.. 
AM_CXXFLAGS = -Wall -Wno-parentheses -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libmcsat_clause.la

libmcsat_clause_la_SOURCES = \
	literal.h \
	literal_table.h \
	clause.h \
	clause.cpp \
	clause_ref.h \
	clause_ref.cpp \
	clause_db.h \
	clause_db.cpp 
	
EXTRA_DIST = 

SUBDIRS = 
