AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-D __STDC_LIMIT_MACROS \
	-D __STDC_FORMAT_MACROS \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../.. 
AM_CXXFLAGS = -Wall -Wno-parentheses -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libmcsat_util.la

libmcsat_util_la_SOURCES = \
	var_priority_queue.h \
	var_priority_queue.cpp \
	assigned_watch_manager.h \
	assigned_watch_manager.cpp
	
EXTRA_DIST = 

SUBDIRS = 

