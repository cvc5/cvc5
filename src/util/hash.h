/*********************                                                        */
/*! \file hash.h
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef __CVC4__HASH_H
#define __CVC4__HASH_H

// in case it's not been declared as a namespace yet
namespace __gnu_cxx {}

#include <ext/hash_map>
#include <ext/hash_set>

namespace __gnu_cxx {

#ifdef CVC4_NEED_HASH_UINT64_T
// on some versions and architectures of GNU C++, we need a
// specialization of hash for 64-bit values
template <>
struct hash<uint64_t> {
  size_t operator()(uint64_t v) const {
    return v;
  }
};/* struct hash<uint64_t> */
#endif /* CVC4_NEED_HASH_UINT64_T */

}/* __gnu_cxx namespace */

// hackish: treat hash stuff as if it were in std namespace
namespace std { using namespace __gnu_cxx; }

namespace CVC4 {

struct StringHashFunction {
  size_t operator()(const std::string& str) const {
    return std::hash<const char*>()(str.c_str());
  }
};/* struct StringHashFunction */

struct StringHashStrategy {
  static size_t hash(const std::string& str) {
    return std::hash<const char*>()(str.c_str());
  }
};/* struct StringHashStrategy */

}/* CVC4 namespace */

#endif /* __CVC4__HASH_H */
