set(bvminisat_src_files
  bvminisat.cpp
  bvminisat.h
  core/Dimacs.h
  core/Solver.cc
  core/Solver.h
  core/SolverTypes.h
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
add_library(bvminisat SHARED ${bvminisat_src_files})
set_target_properties(bvminisat
  PROPERTIES
    COMPILE_DEFINITIONS
      __BUILDING_CVC4LIB
      __STDC_LIMIT_MACROS
      __STDC_FORMAT_MACROS
)
add_dependencies(bvminisat expr)
