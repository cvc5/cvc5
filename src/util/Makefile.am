AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libutil.la libutilcudd.la

# libutilcudd.la is a separate library so that we can pass separate
# compiler flags
libutilcudd_la_CPPFLAGS = $(CPPFLAGS) $(AM_CPPFLAGS) @CUDD_CPPFLAGS@
libutilcudd_la_LIBADD = @CUDD_LDFLAGS@ @CUDD_LIBS@

# Do not list built sources (like integer.h, rational.h, and tls.h) here!
# Rather, list them under BUILT_SOURCES, and their .in versions under
# EXTRA_DIST.  Otherwise, they're packaged up in the tarball, which is
# no good---they belong in the configured builds/ directory.  If they
# end up in the source directory, they build the cvc4 that was
# configured at the time of the "make dist", which (1) may not be the
# configuration that the user wants, and (2) might cause link errors.
libutil_la_SOURCES = \
	Assert.h \
	Assert.cpp \
	backtrackable.h \
	Makefile.am \
	Makefile.in \
	debug.h \
	exception.h \
	hash.h \
	bool.h \
	proof.h \
	output.cpp \
	output.h \
	result.h \
	result.cpp \
	configuration.h \
	configuration_private.h \
	configuration.cpp \
	bitvector.h \
	ascription_type.h \
	array.h \
	datatype.h \
	datatype.cpp \
	matcher.h \
	gmp_util.h \
	sexpr.h \
	sexpr.cpp \
	stats.h \
	stats.cpp \
	dynamic_array.h \
	language.h \
	lemma_input_channel.h \
	lemma_output_channel.h \
	dense_map.h \
	channel.h \
	language.cpp \
	ntuple.h \
	recursion_breaker.h \
	subrange_bound.h \
	dump.h \
	dump.cpp \
	predicate.h \
	predicate.cpp \
	cardinality.h \
	cardinality.cpp \
	cache.h \
	utility.h \
	trans_closure.h \
	trans_closure.cpp \
	boolean_simplification.h \
	boolean_simplification.cpp \
	ite_removal.h \
	ite_removal.cpp \
	node_visitor.h \
	index.h \
	uninterpreted_constant.h \
	uninterpreted_constant.cpp \
	array_store_all.h \
	array_store_all.cpp \
	model.h \
	model.cpp

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
	tls.h.in \
	integer.i \
	stats.i \
	bool.i \
	sexpr.i \
	datatype.i \
	output.i \
	cardinality.i \
	result.i \
	configuration.i \
	Assert.i \
	bitvector.i \
	subrange_bound.i \
	exception.i \
	language.i \
	array.i \
	array_store_all.i \
	ascription_type.i \
	rational.i \
	hash.i

DISTCLEANFILES = \
	integer.h.tmp \
	rational.h.tmp \
	tls.h.tmp \
	integer.h \
	rational.h \
	tls.h
