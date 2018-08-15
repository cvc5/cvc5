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

add_library(minisat ${minisat_src_files})
target_include_directories(minisat PRIVATE .)
target_compile_definitions(minisat
  PRIVATE
    -D__BUILDING_CVC4LIB
    -D__STDC_LIMIT_MACROS
    -D__STDC_FORMAT_MACROS
)
target_link_libraries(minisat expr)
