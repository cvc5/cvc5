SUBDIRS = . java

AM_CPPFLAGS = \
	-I@srcdir@/../../src/include -I@srcdir@/../../src -I@builddir@/../../src $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall
AM_CFLAGS = -Wall

noinst_PROGRAMS = \
	bitvectors \
	bitvectors-new \
	bitvectors_and_arrays \
	bitvectors_and_arrays-new \
	combination \
	combination-new \
	datatypes \
	datatypes-new \
	extract \
	extract-new \
	helloworld \
	helloworld-new \
	linear_arith \
	linear_arith-new \
	sets \
	sets-new \
	strings \
	strings-new

noinst_DATA =

bitvectors_SOURCES = \
	bitvectors.cpp
bitvectors_LDADD = \
	@builddir@/../../src/libcvc4.la
bitvectors_new_SOURCES = \
	bitvectors-new.cpp
bitvectors_new_LDADD = \
	@builddir@/../../src/libcvc4.la

bitvectors_and_arrays_SOURCES = \
	bitvectors_and_arrays.cpp
bitvectors_and_arrays_LDADD = \
	@builddir@/../../src/libcvc4.la
bitvectors_and_arrays_new_SOURCES = \
	bitvectors_and_arrays-new.cpp
bitvectors_and_arrays_new_LDADD = \
	@builddir@/../../src/libcvc4.la

combination_SOURCES = \
	combination.cpp
combination_LDADD = \
	@builddir@/../../src/libcvc4.la
combination_new_SOURCES = \
	combination-new.cpp
combination_new_LDADD = \
	@builddir@/../../src/libcvc4.la

datatypes_SOURCES = \
	datatypes.cpp
datatypes_LDADD = \
	@builddir@/../../src/libcvc4.la
datatypes_new_SOURCES = \
	datatypes-new.cpp
datatypes_new_LDADD = \
	@builddir@/../../src/libcvc4.la

extract_SOURCES = \
	extract.cpp
extract_LDADD = \
	@builddir@/../../src/libcvc4.la
extract_new_SOURCES = \
	extract-new.cpp
extract_new_LDADD = \
	@builddir@/../../src/libcvc4.la

helloworld_SOURCES = \
	helloworld.cpp
helloworld_CXXFLAGS = \
	-DCVC4_MAKE_EXAMPLES
helloworld_LDADD = \
	@builddir@/../../src/libcvc4.la
helloworld_new_SOURCES = \
	helloworld-new.cpp
helloworld_new_CXXFLAGS = \
	-DCVC4_MAKE_EXAMPLES
helloworld_new_LDADD = \
	@builddir@/../../src/libcvc4.la

linear_arith_SOURCES = \
	linear_arith.cpp
linear_arith_LDADD = \
	@builddir@/../../src/libcvc4.la
linear_arith_new_SOURCES = \
	linear_arith-new.cpp
linear_arith_new_LDADD = \
	@builddir@/../../src/libcvc4.la

sets_SOURCES = \
	sets.cpp
sets_LDADD = \
	@builddir@/../../src/libcvc4.la
sets_new_SOURCES = \
	sets-new.cpp
sets_new_LDADD = \
	@builddir@/../../src/libcvc4.la

strings_SOURCES = \
	strings.cpp
strings_LDADD = \
	@builddir@/../../src/libcvc4.la
strings_new_SOURCES = \
	strings-new.cpp
strings_new_LDADD = \
	@builddir@/../../src/libcvc4.la

# for installation
examplesdir = $(docdir)/$(subdir)
examples_DATA = $(DIST_SOURCES) $(EXTRA_DIST)
