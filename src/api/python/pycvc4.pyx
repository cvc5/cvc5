# distutils: language = c++
# distutils: include_dirs = ../ ../include/
# distutils: extra_compile_args = -std=c++11 -D__BUILDING_CVC4LIB
# distutils: libraries = cvc4 cvc4parser

include "kinds.pxi"
include "cvc4.pxi"
