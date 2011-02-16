AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libarith.la

libarith_la_SOURCES = \
	theory_arith_type_rules.h \
	arith_rewriter.h \
	arith_rewriter.cpp \
	normal_form.h\
	normal_form.cpp \
	arith_utilities.h \
	arith_constants.h \
	delta_rational.h \
	delta_rational.cpp \
	partial_model.h \
	partial_model.cpp \
	ordered_bounds_list.h \
	ordered_set.h \
	arithvar_dense_set.h \
	arithvar_set.h \
	tableau.h \
	tableau.cpp \
	simplex.h \
	simplex.cpp \
	row_vector.h \
	row_vector.cpp \
	unate_propagator.h \
	unate_propagator.cpp \
	theory_arith.h \
	theory_arith.cpp

EXTRA_DIST = \
	kinds \
	normal_form_notes.txt
