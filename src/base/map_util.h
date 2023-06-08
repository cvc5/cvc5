/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 * Utility functions for dealing with maps and related classes in a mostly
 * uniform fashion.
 *
 * These are stylistically encouraged (but not required) in new code.
 * Supports:
 * - std::map
 * - std::unordered_map
 * - context::CDHashmap
 * - context::CDInsertHashmap
 * The ContainsKey function is also compatible with std::[unordered_]set.
 *
 * Currently implemented classes of functions:
 * - ContainsKey
 *   Returns true if a map contains a key. (Also Supports std::set and
 *   std::unordered_set.)
 * - FindOr*
 *   Finds an data element mapped to by the map. Variants include FindOrNull
 *   and FindOrDie.
 *
 * Potential future classes of functions:
 * - InsertOrUpdate
 * - InsertIfNotPresent
 */

#include "cvc5_private.h"

#ifndef CVC5__BASE__MAP_UTIL_H
#define CVC5__BASE__MAP_UTIL_H

#include "base/check.h"

namespace cvc5::internal {

// Returns true if the `map` contains the `key`.
//
// Supports sets as well.
template <class M, class Key>
bool ContainsKey(const M& map, const Key& key)
{
  return map.find(key) != map.end();
}

template <typename M>
using MapKeyTypeT = typename M::value_type::first_type;
template <typename M>
using MapMappedTypeT = typename M::value_type::second_type;

// Returns a pointer to the const value mapped by `key` if it exists, or nullptr
// otherwise.
template <class M>
const MapMappedTypeT<M>* FindOrNull(const M& map, const MapKeyTypeT<M>& key)
{
  auto it = map.find(key);
  if (it == map.end())
  {
    return nullptr;
  }
  return &((*it).second);
}

// Returns a pointer to the non-const value mapped by `key` if it exists, or
// nullptr otherwise.
template <class M>
MapMappedTypeT<M>* FindOrNull(M& map, const MapKeyTypeT<M>& key)
{
  auto it = map.find(key);
  if (it == map.end())
  {
    return nullptr;
  }
  return &((*it).second);
}

// Returns a const reference to the value mapped by `key` if it exists. Dies
// if the element is not there.
template <class M>
const MapMappedTypeT<M>& FindOrDie(const M& map, const MapKeyTypeT<M>& key)
{
  auto it = map.find(key);
  AlwaysAssert(it != map.end()) << "The map does not contain the key.";
  return (*it).second;
}

}  // namespace cvc5::internal

#endif /* CVC5__BASE__MAP_UTIL_H */
