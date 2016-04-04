/*********************                                                        */
/*! \file hash.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Christopher L. Conway, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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
    return __gnu_cxx::hash<const char*>()(str.c_str());
  }
};/* struct StringHashFunction */

template <class T, class U, class HashT = std::hash<T>, class HashU = std::hash<U> >
struct PairHashFunction {
  size_t operator()(const std::pair<T, U>& pr) const {
    return HashT()(pr.first) ^ HashU()(pr.second);
  }
};/* struct PairHashFunction */

}/* CVC4 namespace */

#endif /* __CVC4__HASH_H */
