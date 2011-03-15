AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libutil.la libutilcudd.la

# libutilcudd.la is a separate library so that we can pass separate
# compiler flags
libutilcudd_la_CPPFLAGS = $(CPPFLAGS) $(AM_CPPFLAGS) @CUDD_CPPFLAGS@
libutilcudd_la_LIBADD = @CUDD_LDFLAGS@

libutil_la_SOURCES = \
	Assert.h \
	Assert.cpp \
	Makefile.am \
	Makefile.in \
	congruence_closure.h \
	debug.h \
	exception.h \
	hash.h \
	bool.h \
	options.h \
	options.cpp \
	output.cpp \
	output.h \
	result.h \
	result.cpp \
	configuration.h \
	configuration_private.h \
	configuration.cpp \
	rational.h \
	integer.h \
	bitvector.h \
	gmp_util.h \
	sexpr.h \
	stats.h \
	stats.cpp \
	dynamic_array.h \
	language.h \
	triple.h
libutil_la_LIBADD = \
	@builddir@/libutilcudd.la
libutilcudd_la_SOURCES = \
	propositional_query.h \
	propositional_query.cpp

BUILT_SOURCES = \
	rational.h \
	integer.h \
	tls.h

if CVC4_CLN_IMP
libutil_la_SOURCES += \
	rational_cln_imp.cpp
endif
if CVC4_GMP_IMP
libutil_la_SOURCES += \
	rational_gmp_imp.cpp
endif

EXTRA_DIST = \
	rational_cln_imp.h \
	integer_cln_imp.h \
	rational_cln_imp.cpp \
	rational_gmp_imp.h \
	integer_gmp_imp.h \
	rational_gmp_imp.cpp \
	rational.h.in \
	integer.h.in \
	tls.h.in
