AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-D __STDC_LIMIT_MACROS \
	-D __STDC_FORMAT_MACROS \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../.. 
AM_CXXFLAGS = -Wall -Wno-parentheses -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libmcsat_rules.la

libmcsat_rules_la_SOURCES = \
	proof_rule.h \
	proof_rule.cpp \
	input_clause_rule.h \
	input_clause_rule.cpp \
	resolution_rule.h \
	resolution_rule.cpp \
	fourier_motzkin_rule.h \
	fourier_motzkin_rule.cpp \
	int_split_rule.h \
	int_split_rule.cpp \
	ackermann_rule.h \
	ackermann_rule.cpp
	
EXTRA_DIST = 

SUBDIRS = 

