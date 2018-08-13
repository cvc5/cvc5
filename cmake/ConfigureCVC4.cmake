include(CheckCXXSourceCompiles)

# Check whether "long" and "int64_t" are distinct types w.r.t. overloading.
# Even if they have the same size, they can be distinct, and some platforms
# can have problems with ambiguous function calls when auto-converting
# int64_t to long, and others will complain if you overload a function
# that takes an int64_t with one that takes a long (giving a redefinition
# error).  So we have to keep both happy.  Probably the same underlying
# issue as the hash specialization below, but let's check separately
# for flexibility.

check_cxx_source_compiles(
  "#include <stdint.h>
   void foo(long) {}
   void foo(int64_t) {}
   int main() { return 0; }"
  CVC4_NEED_INT64_T_OVERLOADS
)
if(NOT CVC4_NEED_INT64_T_OVERLOADS)
  set(CVC4_NEED_INT64_T_OVERLOADS 0)
endif()

# Check to see if this version/architecture of GNU C++ explicitly
# instantiates std::hash<uint64_t> or not.  Some do, some don't.
# See src/util/hash.h.

check_cxx_source_compiles(
  "#include <cstdint>
   #include <functional>
   namespace std { template<> struct hash<uint64_t> {}; }
   int main() { return 0; }"
  CVC4_NEED_HASH_UINT64_T_OVERLOAD
)
if(CVC4_NEED_HASH_UINT64_T_OVERLOAD)
  add_definitions(-DCVC4_NEED_HASH_UINT64_T)
endif()
