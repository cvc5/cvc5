/*********************                                                        */
/*! \file map_util.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility functions for dealing with maps in a mostly uniform fashion.
 **
 ** Utility functions for dealing with maps and related classed in a mostly
 ** uniform fashion. These are stylistically encouraged (but not required) in
 ** new code. Supports:
 ** - std::map
 ** - std::unordered_map
 ** - CVC4::context::CDHashmap
 ** - CVC4::context::CDInsertHashmap
 ** The ContainsKey function is also compatible with std::[unordered_]set.
 **
 ** Currently implemented classes of functions:
 ** - ContainsKey
 **   Returns true if a map contains a key. (Also Supports std::set and
 **   std::unordered_set.)
 ** - FindOr*
 **   Finds an data element mapped to by the map. Variants include FindOrNull
 **   and FindOrDie.
 **
 ** Potential future classes of functions:
 ** - InsertOrUpdate
 ** - InsertIfNotPresent
 **/

#include "cvc4_private.h"

#ifndef CVC4__BASE__MAP_UTIL_H
#define CVC4__BASE__MAP_UTIL_H

#include "base/check.h"

namespace CVC4 {

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

}  // namespace CVC4

#endif /* CVC4__BASE__MAP_UTIL_H */
