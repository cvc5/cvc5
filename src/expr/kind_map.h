/*********************                                                        */
/*! \file kind_map.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A bitmap of Kinds
 **
 ** This is a class representation for a bitmap of Kinds that is
 ** iterable, manipulable, and packed.
 **/

#include "cvc4_private.h"

#ifndef CVC4__KIND_MAP_H
#define CVC4__KIND_MAP_H

#include <stdint.h>
#include <iterator>

#include "base/check.h"
#include "expr/kind.h"

namespace CVC4 {

/** A bitmap of Kinds. */
class KindMap {
  static const size_t SIZE = (kind::LAST_KIND + 63) / 64;

  uint64_t d_bitmap[SIZE];

  /**
   * Accessor proxy class used so that things like "map[k] = true"
   * will work as expected (we have to return a proxy from
   * KindMap::operator[]() in that case, since we can't construct an
   * address to the individual *bit* in the packed representation).
   */
  class Accessor {
    KindMap& d_map;
    Kind d_kind;

    Accessor(KindMap& m, Kind k) :
      d_map(m),
      d_kind(k) {
      AssertArgument(k >= Kind(0) && k < kind::LAST_KIND, k, "invalid kind");
    }

    friend class KindMap;

  public:

    operator bool() const {
      return d_map.tst(d_kind);
    }

    Accessor operator=(bool b) const {
      if(b) {
        d_map.set(d_kind);
      } else {
        d_map.clr(d_kind);
      }
      return *this;
    }

  };/* class KindMap::Accessor */

public:

  /** An iterator over a KindMap. */
  class iterator {
    const KindMap* d_map;
    Kind d_kind;

  public:
    typedef std::input_iterator_tag iterator_category;
    typedef Kind value_type;

    iterator() :
      d_map(NULL),
      d_kind(Kind(0)) {
    }
    iterator(const KindMap& m, Kind k) :
      d_map(&m),
      d_kind(k) {
      AssertArgument(k >= Kind(0) && k <= kind::LAST_KIND, k, "invalid kind");
      while(d_kind < kind::LAST_KIND &&
            ! d_map->tst(d_kind)) {
        d_kind = Kind(uint64_t(d_kind) + 1);
      }
    }
    iterator& operator++() {
      if(d_kind < kind::LAST_KIND) {
        d_kind = Kind(uint64_t(d_kind) + 1);
        while(d_kind < kind::LAST_KIND &&
              ! d_map->tst(d_kind)) {
          d_kind = Kind(uint64_t(d_kind) + 1);
        }
      }
      return *this;
    }
    iterator operator++(int) const {
      const_iterator i = *this;
      ++i;
      return i;
    }
    Kind operator*() const {
      return d_kind;
    }
    bool operator==(iterator i) const {
      return d_map == i.d_map && d_kind == i.d_kind;
    }
    bool operator!=(iterator i) const {
      return !(*this == i);
    }
  };/* class KindMap::iterator */
  typedef iterator const_iterator;

  KindMap() {
    clear();
  }
  KindMap(const KindMap& m) {
    for(unsigned i = 0; i < SIZE; ++i) {
      d_bitmap[i] = m.d_bitmap[i];
    }
  }
  KindMap(Kind k) {
    clear();
    set(k);
  }

  /** Empty the map. */
  void clear() {
    for(unsigned i = 0; i < SIZE; ++i) {
      d_bitmap[i] = uint64_t(0);
    }
  }
  /** Tests whether the map is empty. */
  bool isEmpty() const {
    for(unsigned i = 0; i < SIZE; ++i) {
      if(d_bitmap[i] != uint64_t(0)) {
        return false;
      }
    }
    return true;
  }
  /** Test whether k is in the map. */
  bool tst(Kind k) const {
    AssertArgument(k >= Kind(0) && k < kind::LAST_KIND, k, "invalid kind");
    return (d_bitmap[k / 64] >> (k % 64)) & uint64_t(1);
  }
  /** Set k in the map. */
  void set(Kind k) {
    AssertArgument(k >= Kind(0) && k < kind::LAST_KIND, k, "invalid kind");
    d_bitmap[k / 64] |= (uint64_t(1) << (k % 64));
  }
  /** Clear k from the map. */
  void clr(Kind k) {
    AssertArgument(k >= Kind(0) && k < kind::LAST_KIND, k, "invalid kind");
    d_bitmap[k / 64] &= ~(uint64_t(1) << (k % 64));
  }

  /** Iterate over the map. */
  const_iterator begin() const {
    return const_iterator(*this, Kind(0));
  }
  const_iterator end() const {
    return const_iterator(*this, kind::LAST_KIND);
  }

  /** Invert the map. */
  KindMap operator~() const {
    KindMap r;
    for(unsigned i = 0; i < SIZE; ++i) {
      r.d_bitmap[i] = ~d_bitmap[i];
    }
    return r;
  }
  /** Bitwise-AND the map (with assignment). */
  KindMap& operator&=(const KindMap& m) {
    for(unsigned i = 0; i < SIZE; ++i) {
      d_bitmap[i] &= m.d_bitmap[i];
    }
    return *this;
  }
  /** Bitwise-AND the map. */
  KindMap operator&(const KindMap& m) const {
    KindMap r(*this);
    r &= m;
    return r;
  }
  /** Bitwise-OR the map (with assignment). */
  KindMap& operator|=(const KindMap& m) {
    for(unsigned i = 0; i < SIZE; ++i) {
      d_bitmap[i] |= m.d_bitmap[i];
    }
    return *this;
  }
  /** Bitwise-OR the map. */
  KindMap operator|(const KindMap& m) const {
    KindMap r(*this);
    r |= m;
    return r;
  }
  /** Bitwise-XOR the map (with assignment). */
  KindMap& operator^=(const KindMap& m) {
    for(unsigned i = 0; i < SIZE; ++i) {
      d_bitmap[i] ^= m.d_bitmap[i];
    }
    return *this;
  }
  /** Bitwise-XOR the map. */
  KindMap operator^(const KindMap& m) const {
    KindMap r(*this);
    r ^= m;
    return r;
  }

  /** Test whether k is in the map. */
  bool operator[](Kind k) const {
    return tst(k);
  }
  /** Test whether k is in the map (allowing assignment). */
  Accessor operator[](Kind k) {
    return Accessor(*this, k);
  }

  /** Test equality between two maps. */
  bool operator==(KindMap m) {
    for(unsigned i = 0; i < SIZE; ++i) {
      if(d_bitmap[i] != m.d_bitmap[i]) {
        return false;
      }
    }
    return true;
  }
  bool operator!=(KindMap m) {
    return !(*this == m);
  }
};/* class KindMap */

inline KindMap operator~(Kind k) {
  KindMap m(k);
  return ~m;
}
inline KindMap operator&(Kind k1, Kind k2) {
  KindMap m(k1);
  return m &= k2;
}
inline KindMap operator&(Kind k1, KindMap m2) {
  return m2 & k1;
}
inline KindMap operator|(Kind k1, Kind k2) {
  KindMap m(k1);
  return m |= k2;
}
inline KindMap operator|(Kind k1, KindMap m2) {
  return m2 | k1;
}
inline KindMap operator^(Kind k1, Kind k2) {
  KindMap m(k1);
  return m ^= k2;
}
inline KindMap operator^(Kind k1, KindMap m2) {
  return m2 ^ k1;
}

}/* CVC4 namespace */

#endif /* CVC4__KIND_MAP_H */
