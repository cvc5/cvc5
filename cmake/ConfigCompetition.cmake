set(CVC4_BUILD_PROFILE_COMPETITION 1)
add_definitions(-DCVC4_COMPETITION_MODE)
add_check_c_cxx_flag("-funroll-all-loops")
add_check_c_cxx_flag("-fexpensive-optimizations")
add_check_c_cxx_flag("-fno-enforce-eh-specs")
# OPTLEVEL=9
# enable_optimized=yes
set(OPTIMIZATION_LEVEL, 9)
# enable_debug_symbols=no
# enable_statistics=no
# enable_replay=no
# enable_assertions=no
# enable_proof=no
# enable_tracing=no
# enable_dumping=no
# enable_muzzle=yes
set(ENABLE_MUZZLE ON)
# enable_valgrind=no
# enable_shared=no
