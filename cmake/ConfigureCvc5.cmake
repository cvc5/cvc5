###############################################################################
# Top contributors (to current version):
#   Mathias Preiner, Gereon Kremer, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##

include(CheckCXXSourceCompiles)
include(CheckIncludeFile)
include(CheckIncludeFileCXX)
include(CheckSymbolExists)
include(CheckLibraryExists)

# Check whether "long" and "int64_t" are distinct types w.r.t. overloading.
# Even if they have the same size, they can be distinct, and some platforms
# can have problems with ambiguous function calls when auto-converting
# int64_t to long, and others will complain if you overload a function
# that takes an int64_t with one that takes a long (giving a redefinition
# error).  So we have to keep both happy.  Probably the same underlying
# issue as the hash specialization below, but let's check separately
# for flexibility.
check_cxx_source_compiles(
  "
  #include <stdint.h>
  void foo(long) {}
  void foo(int64_t) {}
  int main() { return 0; }
  "
  CVC5_NEED_INT64_T_OVERLOADS
)
if(NOT CVC5_NEED_INT64_T_OVERLOADS)
  set(CVC5_NEED_INT64_T_OVERLOADS 0)
endif()

# Check to see if this version/architecture of GNU C++ explicitly
# instantiates std::hash<uint64_t> or not.  Some do, some don't.
# See src/util/hash.h.
check_cxx_source_compiles(
  "
  #include <cstdint>
  #include <functional>
  namespace std { template<> struct hash<uint64_t> {}; }
  int main() { return 0; }
  "
  CVC5_NEED_HASH_UINT64_T_OVERLOAD
)
if(CVC5_NEED_HASH_UINT64_T_OVERLOAD)
  add_definitions(-DCVC5_NEED_HASH_UINT64_T)
endif()

check_include_file(unistd.h HAVE_UNISTD_H)
check_include_file(sys/wait.h HAVE_SYS_WAIT_H)
check_include_file_cxx(ext/stdio_filebuf.h HAVE_EXT_STDIO_FILEBUF_H)

# For Windows builds check if clock_gettime is available via -lpthread
# (pthread_time.h).
if(CMAKE_SYSTEM_NAME STREQUAL "Windows")
  set(CMAKE_REQUIRED_FLAGS -pthread)
  check_symbol_exists(clock_gettime "time.h" HAVE_CLOCK_GETTIME)
  unset(CMAKE_REQUIRED_FLAGS)
  if(HAVE_CLOCK_GETTIME)
    add_c_cxx_flag(-pthread)
  endif()
else()
  check_symbol_exists(clock_gettime "time.h" HAVE_CLOCK_GETTIME)
  if(NOT HAVE_CLOCK_GETTIME)
    unset(HAVE_CLOCK_GETTIME CACHE)
    check_library_exists(rt clock_gettime "time.h" HAVE_CLOCK_GETTIME)
    find_library(RT_LIBRARIES NAMES rt)
  endif()
endif()
check_symbol_exists(ffs "strings.h" HAVE_FFS)
check_symbol_exists(optreset "getopt.h" HAVE_DECL_OPTRESET)
check_symbol_exists(sigaltstack "signal.h" HAVE_SIGALTSTACK)
check_symbol_exists(strerror_r "string.h" HAVE_STRERROR_R)
check_symbol_exists(strtok_r "string.h" HAVE_STRTOK_R)
check_symbol_exists(setitimer "sys/time.h" HAVE_SETITIMER)

# on non-POSIX systems, time limit is implemented with threads
if(NOT HAVE_SETITIMER)
  find_package(Threads REQUIRED)
  set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${CMAKE_THREAD_LIBS_INIT}")
endif()

# Determine if we have the POSIX (int) or GNU (char *) variant of strerror_r.
check_c_source_compiles(
  "
  #include <string.h>
  int main(void)
  {
    char buf[1];
    char c = *strerror_r(0, buf, 0);
    return 0;
  }
  "
  STRERROR_R_CHAR_P
)

# Defined if using the CLN multi-precision arithmetic library.
set(CVC5_CLN_IMP ${CVC5_USE_CLN_IMP})
# Defined if using the GMP multi-precision arithmetic library.
set(CVC5_GMP_IMP ${CVC5_USE_GMP_IMP})
# Defined if using the libpoly polynomial library.
set(CVC5_POLY_IMP ${CVC5_USE_POLY_IMP})
# Define the full name of this package.
set(CVC5_PACKAGE_NAME "${PROJECT_NAME}")
