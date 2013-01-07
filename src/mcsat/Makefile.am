AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-D __STDC_LIMIT_MACROS \
	-D __STDC_FORMAT_MACROS \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/.. 
AM_CXXFLAGS = -Wall -Wno-parentheses -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libmcsat.la

libmcsat_la_SOURCES = \
	solver_trail.h \
	solver_trail.cpp \
	solver.h \
	solver.cpp \
	mcsat.h \
	mcsat.cpp \
	prop_engine.h \
	prop_engine.cpp

libmcsat_la_LIBADD = \
	@builddir@/clause/libmcsat_clause.la \
	@builddir@/rules/libmcsat_rules.la \
	@builddir@/util/libmcsat_util.la \
	@builddir@/plugin/libmcsat_solver_plugin.la \
	@builddir@/variable/libmcsat_variable.la \
	@builddir@/cnf/libmcsat_cnf.la \
	@builddir@/bcp/libmcsat_bcp.la \
	@builddir@/fm/libmcsat_fm.la \
	@builddir@/uf/libmcsat_uf.la 

EXTRA_DIST = 

SUBDIRS = variable clause util rules plugin cnf bcp fm uf . 

