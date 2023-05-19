/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * cvc5 hash utilities.
 */

#include "cvc5_public.h"

#ifndef CVC5__HASH_H
#define CVC5__HASH_H

#include <functional>
#include <string>

namespace std {

#ifdef CVC5_NEED_HASH_UINT64_T
// on some versions and architectures of GNU C++, we need a
// specialization of hash for 64-bit values
template <>
struct hash<uint64_t> {
  size_t operator()(uint64_t v) const {
    return v;
  }
};/* struct hash<uint64_t> */
#endif /* CVC5_NEED_HASH_UINT64_T */

}/* std namespace */

namespace cvc5::internal {

namespace fnv1a {

constexpr uint64_t offsetBasis = 14695981039346656037U;

/**
 * FNV-1a hash algorithm for 64-bit numbers.
 *
 * More details here: http://www.isthe.com/chongo/tech/comp/fnv/index.html
 */
inline uint64_t fnv1a_64(uint64_t v, uint64_t hash = offsetBasis)
{
  hash ^= v;
  // Compute (hash * 1099511628211)
  return hash + (hash << 1) + (hash << 4) + (hash << 5) + (hash << 7) +
         (hash << 8) + (hash << 40);
}

}  // namespace fnv1a

template <class T, class U, class HashT = std::hash<T>, class HashU = std::hash<U> >
struct PairHashFunction {
  size_t operator()(const std::pair<T, U>& pr) const {
    uint64_t hash = fnv1a::fnv1a_64(HashT()(pr.first));
    return static_cast<size_t>(fnv1a::fnv1a_64(HashU()(pr.second), hash));
  }
};/* struct PairHashFunction */

}  // namespace cvc5::internal

#endif /* CVC5__HASH_H */
