AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/mtl -I@srcdir@/core -I@srcdir@/../../include
AM_CXXFLAGS = -Wall -fvisibility=hidden

noinst_LTLIBRARIES = libminisat.la
libminisat_la_SOURCES = \
	core/Solver.C \
	core/Solver.h \
	core/SolverTypes.h \
	simp/SimpSolver.C \
	simp/SimpSolver.h \
	mtl/Alg.h \
	mtl/BasicHeap.h \
	mtl/BoxedVec.h \
	mtl/Heap.h \
	mtl/Map.h \
	mtl/Queue.h \
	mtl/Sort.h \
	mtl/Vec.h

EXTRA_DIST = \
	core/Main.C \
	core/Makefile \
	simp/Main.C \
	simp/Makefile \
	README \
	LICENSE \
	mtl/template.mk
