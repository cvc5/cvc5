set(CVC4_BUILD_PROFILE_DEBUG 1)
add_definitions(-DCVC4_DEBUG)
set(CVC4_DEBUG 1)
add_check_c_cxx_flag("-fno-inline")
# enable_optimized=no
add_c_cxx_flag("-Og")
# enable_debug_symbols=yes
set(ENABLE_DEBUG_SYMBOLS ON)
# enable_statistics=yes
set(ENABLE_STATISTICS ON)
# enable_replay=yes
set(ENABLE_REPLAY ON)
# enable_assertions=yes
set(ENABLE_ASSERTIONS ON)
# enable_proof=yes
set(ENABLE_PROOFS, ON)
# enable_tracing=yes
set(ENABLE_TRACING ON)
# enable_dumping=yes
set(ENABLE_DUMPING ON)
# enable_muzzle=no
# enable_valgrind=optional
