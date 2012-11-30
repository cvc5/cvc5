AM_CPPFLAGS = \
	-I@srcdir@/../../src/include -I@srcdir@/../../src -I@builddir@/../../src $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall
AM_CFLAGS = -Wall

noinst_PROGRAMS = \
	linear_arith \
	helloworld \
	combination


noinst_DATA =

linear_arith_SOURCES = \
	linear_arith.cpp
linear_arith_LDADD = \
	@builddir@/../../src/libcvc4.la


combination_SOURCES = \
	combination.cpp
combination_LDADD = \
	@builddir@/../../src/libcvc4.la

helloworld_SOURCES = \
	helloworld.cpp
helloworld_LDADD = \
	@builddir@/../../src/libcvc4.la

# for installation
examplesdir = $(docdir)/$(subdir)
examples_DATA = $(DIST_SOURCES) $(EXTRA_DIST)
