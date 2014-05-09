AM_CPPFLAGS = \
	-I@srcdir@/../../src/include -I@srcdir@/../../src -I@builddir@/../../src $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall
AM_CFLAGS = -Wall

noinst_PROGRAMS = \
	sha1_inversion \
	sha1_collision

noinst_DATA =

sha1_inversion_SOURCES = \
	sha1_inversion.cpp \
	word.h \
	word.cpp \
	sha1.hpp
sha1_inversion_LDADD = \
	@builddir@/../../src/libcvc4.la

sha1_collision_SOURCES = \
	sha1_collision.cpp \
	word.h \
	word.cpp \
	sha1.hpp
sha1_collision_LDADD = \
	@builddir@/../../src/libcvc4.la


# for installation
examplesdir = $(docdir)/$(subdir)
examples_DATA = \
	sha1_inversion.cpp \
	sha1_collision.cpp \
	word.h \
	word.cpp \
	sha1.hpp
