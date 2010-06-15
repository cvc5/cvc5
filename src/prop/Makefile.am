AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libprop.la

libprop_la_SOURCES = \
	prop_engine.cpp \
	prop_engine.h \
	sat.h \
        sat.cpp \
	cnf_stream.h \
	cnf_stream.cpp \
	cnf_conversion.h

SUBDIRS = minisat
