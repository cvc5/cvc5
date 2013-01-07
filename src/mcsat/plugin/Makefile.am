AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-D __STDC_LIMIT_MACROS \
	-D __STDC_FORMAT_MACROS \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../.. 
AM_CXXFLAGS = -Wall -Wno-parentheses -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libmcsat_solver_plugin.la

libmcsat_solver_plugin_la_SOURCES = \
  solver_plugin.h \
  solver_plugin.cpp \
  solver_plugin_notify.h \
  solver_plugin_notify.cpp \
  solver_plugin_features.h \
  solver_plugin_features.cpp \
  solver_plugin_registry.h \
  solver_plugin_registry.cpp \
  solver_plugin_factory.h \
  solver_plugin_factory.cpp
     
EXTRA_DIST = 

SUBDIRS = 

