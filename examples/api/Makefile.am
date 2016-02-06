SUBDIRS = . java

AM_CPPFLAGS = \
	-I@srcdir@/../../src/include -I@srcdir@/../../src -I@builddir@/../../src $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall
AM_CFLAGS = -Wall

noinst_PROGRAMS = \
	bitvectors \
	bitvectors_and_arrays \
	combination \
	datatypes \
        extract \
	helloworld \
	linear_arith \
	sets \
	strings

noinst_DATA =

bitvectors_SOURCES = \
	bitvectors.cpp
bitvectors_LDADD = \
	@builddir@/../../src/libcvc4.la

bitvectors_and_arrays_SOURCES = \
	bitvectors_and_arrays.cpp
bitvectors_and_arrays_LDADD = \
	@builddir@/../../src/libcvc4.la

combination_SOURCES = \
	combination.cpp
combination_LDADD = \
	@builddir@/../../src/libcvc4.la

datatypes_SOURCES = \
	datatypes.cpp
datatypes_LDADD = \
	@builddir@/../../src/libcvc4.la

extract_SOURCES = \
	extract.cpp
extract_LDADD = \
	@builddir@/../../src/libcvc4.la

helloworld_SOURCES = \
	helloworld.cpp
helloworld_CXXFLAGS = \
	-DCVC4_MAKE_EXAMPLES
helloworld_LDADD = \
	@builddir@/../../src/libcvc4.la

linear_arith_SOURCES = \
	linear_arith.cpp
linear_arith_LDADD = \
	@builddir@/../../src/libcvc4.la

sets_SOURCES = \
	sets.cpp
sets_LDADD = \
	@builddir@/../../src/libcvc4.la

strings_SOURCES = \
	strings.cpp
strings_LDADD = \
	@builddir@/../../src/libcvc4.la

# for installation
examplesdir = $(docdir)/$(subdir)
examples_DATA = $(DIST_SOURCES) $(EXTRA_DIST)
