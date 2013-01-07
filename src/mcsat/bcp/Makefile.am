AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-D __STDC_LIMIT_MACROS \
	-D __STDC_FORMAT_MACROS \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../.. 
AM_CXXFLAGS = -Wall -Wno-parentheses -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libmcsat_bcp.la

libmcsat_bcp_la_SOURCES = \
	bcp_engin.h \
	bcp_engine.cpp \
	watch_list_manager.h \
	watch_list_manager.cpp
	
EXTRA_DIST = 

SUBDIRS = 
