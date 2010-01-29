AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -fvisibility=hidden

noinst_LTLIBRARIES = libsmt.la

libsmt_la_SOURCES = \
	smt_engine.cpp \
	smt_engine.h \
	cnf_converter.h \
	cnf_converter.cpp \
	cnf_conversion.h
