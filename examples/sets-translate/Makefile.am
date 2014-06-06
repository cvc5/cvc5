AM_CPPFLAGS = \
	-I@srcdir@/../../src/include -I@srcdir@/../../src -I@builddir@/../../src $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall
AM_CFLAGS = -Wall

noinst_PROGRAMS = \
	sets_translate	

noinst_DATA =

sets_translate_SOURCES = \
	sets_translate.cpp
sets_translate_LDADD = \
	@builddir@/../../src/parser/libcvc4parser.la \
	@builddir@/../../src/libcvc4.la

# for installation
examplesdir = $(docdir)/$(subdir)
examples_DATA = $(DIST_SOURCES) $(EXTRA_DIST)
