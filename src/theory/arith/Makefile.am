AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libarith.la

libarith_la_SOURCES = \
	theory_arith_type_rules.h \
	type_enumerator.h \
	arithvar.h \
	arith_rewriter.h \
	arith_rewriter.cpp \
	arith_static_learner.h \
	arith_static_learner.cpp \
	arithvar_node_map.h \
	constraint_forward.h \
	constraint.h \
	constraint.cpp \
	congruence_manager.h \
	congruence_manager.cpp \
	normal_form.h\
	normal_form.cpp \
	arith_utilities.h \
	delta_rational.h \
	delta_rational.cpp \
	partial_model.h \
	partial_model.cpp \
	linear_equality.h \
	linear_equality.cpp \
	matrix.h \
	matrix.cpp \
	arith_priority_queue.h \
	arith_priority_queue.cpp \
	simplex.h \
	simplex.cpp \
	theory_arith.h \
	theory_arith.cpp \
	dio_solver.h \
	dio_solver.cpp \
	theory_arith_instantiator.h \
	theory_arith_instantiator.cpp

EXTRA_DIST = \
	kinds
