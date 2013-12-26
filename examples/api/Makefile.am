SUBDIRS = . java

AM_CPPFLAGS = \
	-I@srcdir@/../../src/include -I@srcdir@/../../src -I@builddir@/../../src $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall
AM_CFLAGS = -Wall

noinst_PROGRAMS = \
	linear_arith \
	helloworld \
	combination \
	bitvectors \
	bitvectors_and_arrays \
	datatypes

noinst_DATA =

linear_arith_SOURCES = \
	linear_arith.cpp
linear_arith_LDADD = \
	@builddir@/../../src/libcvc4.la

bitvectors_and_arrays_SOURCES = \
	bitvectors_and_arrays.cpp
bitvectors_and_arrays_LDADD = \
	@builddir@/../../src/libcvc4.la

combination_SOURCES = \
	combination.cpp
combination_LDADD = \
	@builddir@/../../src/libcvc4.la

helloworld_SOURCES = \
	helloworld.cpp
helloworld_LDADD = \
	@builddir@/../../src/libcvc4.la

bitvectors_SOURCES = \
	bitvectors.cpp
bitvectors_LDADD = \
	@builddir@/../../src/libcvc4.la

datatypes_SOURCES = \
	datatypes.cpp
datatypes_LDADD = \
	@builddir@/../../src/libcvc4.la

# for installation
examplesdir = $(docdir)/$(subdir)
examples_DATA = $(DIST_SOURCES) $(EXTRA_DIST)
