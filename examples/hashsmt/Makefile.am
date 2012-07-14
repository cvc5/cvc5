AM_CPPFLAGS = \
	-I@srcdir@/../../src/include -I@srcdir@/../../src -I@builddir@/../../src $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall
AM_CFLAGS = -Wall

noinst_PROGRAMS = \
	sha1smt	

noinst_DATA =

sha1smt_SOURCES = \
	sha1smt.cpp \
	word.h \
	word.cpp \
	sha1.hpp
sha1smt_LDADD = \
	@builddir@/../../src/libcvc4.la
