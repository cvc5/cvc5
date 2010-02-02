AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -fvisibility=hidden

noinst_LTLIBRARIES = libprop.la

libprop_la_SOURCES = \
	prop_engine.cpp \
	prop_engine.h \
	sat.h \
	cnf_stream.h \
	cnf_stream.cpp \
	cnf_conversion.h

SUBDIRS = minisat
