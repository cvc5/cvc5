INCLUDES = -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -fvisibility=hidden
AM_CPPFLAGS = -D__BUILDING_CVC4LIB

noinst_LTLIBRARIES = libprop.la

libprop_la_SOURCES = \
	prop_engine.cpp \
	prop_engine.h \
	sat.h

SUBDIRS = minisat
