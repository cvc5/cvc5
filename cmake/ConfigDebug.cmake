add_definitions(-DCVC4_DEBUG)
set(CVC4_DEBUG 1)
add_check_c_cxx_flag("-fno-inline")
# enable_optimized=no
cvc4_set_option(ENABLE_OPTIMIZED OFF)
set(OPTIMIZATION_LEVEL 0)
add_c_cxx_flag("-Og")
# enable_debug_symbols=yes
cvc4_set_option(ENABLE_DEBUG_SYMBOLS ON)
# enable_statistics=yes
cvc4_set_option(ENABLE_STATISTICS ON)
# enable_replay=yes
cvc4_set_option(ENABLE_REPLAY ON)
# enable_assertions=yes
cvc4_set_option(ENABLE_ASSERTIONS ON)
# enable_proof=yes
cvc4_set_option(ENABLE_PROOFS ON)
# enable_tracing=yes
cvc4_set_option(ENABLE_TRACING ON)
# enable_dumping=yes
cvc4_set_option(ENABLE_DUMPING ON)
# enable_muzzle=no
cvc4_set_option(ENABLE_MUZZLE OFF)
# enable_valgrind=optional
cvc4_set_option(ENABLE_UNIT_TESTING ON)
