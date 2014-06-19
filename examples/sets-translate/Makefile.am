AM_CPPFLAGS = \
	-I@srcdir@/../../src/include -I@srcdir@/../../src -I@builddir@/../../src $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall
AM_CFLAGS = -Wall

noinst_PROGRAMS = \
	sets2arrays \
	sets2axioms

noinst_DATA =

sets2arrays_SOURCES = \
	sets_translate.cpp
sets2arrays_LDADD = \
	@builddir@/../../src/parser/libcvc4parser.la \
	@builddir@/../../src/libcvc4.la

# give nodist_: only distribute/install once
nodist_sets2axioms_SOURCES = \
	sets_translate.cpp
sets2axioms_LDADD = \
	@builddir@/../../src/parser/libcvc4parser.la \
	@builddir@/../../src/libcvc4.la
sets2axioms_CXXFLAGS = \
	-DENABLE_AXIOMS

# for installation
examplesdir = $(docdir)/$(subdir)
examples_DATA = $(DIST_SOURCES) $(EXTRA_DIST)
