AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/../.. -I@srcdir@/../../include -I@srcdir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libidl.la

libidl_la_SOURCES = \
	idl_model.h \
	idl_model.cpp \
	idl_assertion.h \
	idl_assertion.cpp \
	idl_assertion_db.h \
	idl_assertion_db.cpp \
	theory_idl.h \
	theory_idl.cpp

EXTRA_DIST = \
	kinds 
