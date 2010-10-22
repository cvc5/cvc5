AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libutil.la

libutil_la_SOURCES = \
	Assert.h \
	Assert.cpp \
	Makefile.am \
	Makefile.in \
	congruence_closure.h \
	debug.h \
	decision_engine.cpp \
	decision_engine.h \
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
	bitvector.cpp \
	gmp_util.h \
	sexpr.h \
	stats.h \
	stats.cpp \
	dynamic_array.h \
	language.h

BUILT_SOURCES = \
	rational.h \
	integer.h \
	tls.h

if CVC4_CLN_IMP
libutil_la_SOURCES += \
	integer_cln_imp.cpp \
	rational_cln_imp.cpp
endif
if CVC4_GMP_IMP
libutil_la_SOURCES += \
	integer_gmp_imp.cpp \
	rational_gmp_imp.cpp
endif

EXTRA_DIST = \
	rational_cln_imp.h \
	integer_cln_imp.h \
	rational_cln_imp.cpp \
	integer_cln_imp.cpp \
	rational_gmp_imp.h \
	integer_gmp_imp.h \
	rational_gmp_imp.cpp \
	integer_gmp_imp.cpp \
	rational.h.in \
	integer.h.in \
	tls.h.in
