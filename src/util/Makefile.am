AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/.. -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libutil.la libstatistics.la

libstatistics_la_CPPFLAGS = $(CPPFLAGS) $(AM_CPPFLAGS) -D__BUILDING_STATISTICS_FOR_EXPORT

# Do not list built sources (like integer.h, rational.h, and tls.h) here!
# Rather, list them under BUILT_SOURCES, and their .in versions under
# EXTRA_DIST.  Otherwise, they're packaged up in the tarball, which is
# no good---they belong in the configured builds/ directory.  If they
# end up in the source directory, they build the cvc4 that was
# configured at the time of the "make dist", which (1) may not be the
# configuration that the user wants, and (2) might cause link errors.
libutil_la_SOURCES = \
	cvc4_assert.h \
	cvc4_assert.cpp \
	backtrackable.h \
	Makefile.am \
	Makefile.in \
	debug.h \
	exception.h \
	exception.cpp \
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
	tuple.h \
	record.h \
	record.cpp \
	divisible.h \
	divisible.cpp \
	maybe.h \
	matcher.h \
	gmp_util.h \
	sexpr.h \
	sexpr.cpp \
	statistics.h \
	statistics.cpp \
	statistics_registry.h \
	statistics_registry.cpp \
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
	nary_builder.h \
	nary_builder.cpp \
	node_visitor.h \
	chain.h \
	index.h \
	uninterpreted_constant.h \
	uninterpreted_constant.cpp \
	abstract_value.h \
	abstract_value.cpp \
	array_store_all.h \
	array_store_all.cpp \
	emptyset.h \
	emptyset.cpp \
	model.h \
	model.cpp \
	sort_inference.h \
	sort_inference.cpp \
	regexp.h

libstatistics_la_SOURCES = \
	statistics_registry.h \
	statistics_registry.cpp

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
	statistics.i \
	bool.i \
	sexpr.i \
	datatype.i \
	tuple.i \
	record.i \
	divisible.i \
	cardinality.i \
	result.i \
	configuration.i \
	bitvector.i \
	subrange_bound.i \
	exception.i \
	language.i \
	array.i \
	array_store_all.i \
	ascription_type.i \
	rational.i \
	hash.i \
	predicate.i \
	uninterpreted_constant.i \
	chain.i \
	regexp.i \
	proof.i

DISTCLEANFILES = \
	integer.h.tmp \
	rational.h.tmp \
	tls.h.tmp \
	integer.h \
	rational.h \
	tls.h
