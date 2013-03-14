AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-D __STDC_LIMIT_MACROS \
	-D __STDC_FORMAT_MACROS \
	-I@builddir@/.. -I@srcdir@/../prop/minisat -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -Wno-parentheses -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libproof.la

libproof_la_SOURCES = \
	proof.h \
	sat_proof.h \
	sat_proof.cpp \
	cnf_proof.h \
	cnf_proof.cpp \
	proof_manager.h \
	proof_manager.cpp

EXTRA_DIST =
