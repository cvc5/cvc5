AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libdecision.la

libdecision_la_SOURCES = \
	decision_engine.h \
	decision_engine.cpp \
	decision_strategy.h \
	justification_heuristic.h \
	justification_heuristic.cpp \
	relevancy.h \
	relevancy.cpp
