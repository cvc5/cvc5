AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-D __STDC_LIMIT_MACROS \
	-D __STDC_FORMAT_MACROS \               	
	-I@srcdir@/ -I@srcdir@/../.. -I@builddir@/../.. -I@srcdir@/../../include
AM_CXXFLAGS = -Wall -Wno-parentheses -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN) -DNDEBUG

noinst_LTLIBRARIES = libminisat.la
libminisat_la_SOURCES = \
	core/Dimacs.h \
	core/Solver.cc \
	core/Solver.h \
	core/SolverTypes.h \
	simp/SimpSolver.cc \
	simp/SimpSolver.h \
	mtl/Alg.h \
	mtl/Alloc.h \
	mtl/Heap.h \
	mtl/IntTypes.h \
	mtl/Map.h \
	mtl/Queue.h \
	mtl/Sort.h \
	mtl/Vec.h \
	mtl/Xalloc.h \
	util/Options.h 

EXTRA_DIST = \
	core/Main.cc \
	core/Makefile \
	doc/ReleaseNotes-2.2.0.txt \
	simp/Main.cc \
	simp/Makefile \
	README \
	LICENSE \
	mtl/config.mk \
	mtl/template.mk \
	utils/ParseUtils.h \
	utils/System.h \
	utils/System.cc \
	Makefile

