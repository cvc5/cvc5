set(minisat_src_files
  core/Dimacs.h
  core/Solver.cc
  core/Solver.h
  core/SolverTypes.h
  minisat.cpp
  minisat.h
  mtl/Alg.h
  mtl/Alloc.h
  mtl/Heap.h
  mtl/IntTypes.h
  mtl/Map.h
  mtl/Queue.h
  mtl/Sort.h
  mtl/Vec.h
  mtl/XAlloc.h
  simp/SimpSolver.cc
  simp/SimpSolver.h
  utils/Options.h
)

include_directories(.)
add_library(minisat SHARED ${minisat_src_files})
set_target_properties(minisat
  PROPERTIES
    COMPILE_DEFINITIONS
      __BUILDING_CVC4LIB
      __STDC_LIMIT_MACROS
      __STDC_FORMAT_MACROS
)
add_dependencies(minisat expr)
