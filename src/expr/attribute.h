/*********************                                                        */
/** attribute.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Node attributes.
 **
 ** Attribute structures:
 **
 ** An attribute structure looks like the following:
 **
 ** struct VarNameAttr {
 **
 **   // the value type for this attribute
 **   typedef std::string value_type;
 **
 **   // an extra hash value (to avoid same-value-type collisions)
 **   enum { hash_value = 1 };
 **
 **   // cleanup routine when the Node goes away
 **   static inline void cleanup(const std::string&) {
 **   }
 ** }
 **/

/* There are strong constraints on ordering of declarations of
 * attributes and nodes due to template use */
#include "expr/node.h"

#ifndef __CVC4__EXPR__ATTRIBUTE_H
#define __CVC4__EXPR__ATTRIBUTE_H

#include <stdint.h>

#include <string>
#include <ext/hash_map>

#include "config.h"
#include "context/context.h"
#include "expr/soft_node.h"
#include "expr/type.h"

#include "util/output.h"

namespace CVC4 {
namespace expr {

// ATTRIBUTE HASH FUNCTIONS ====================================================

struct AttrHashFcn {
  enum { LARGE_PRIME = 1 };
  std::size_t operator()(const std::pair<uint64_t, SoftNode>& p) const {
    return p.first * LARGE_PRIME + p.second.hash();
  }
};

struct AttrHashBoolFcn {
  std::size_t operator()(const SoftNode& n) const {
    return n.hash();
  }
};

// ATTRIBUTE TYPE MAPPINGS =====================================================

template <class T>
struct KindValueToTableValueMapping {
  typedef T table_value_type;
  inline static T convert(const T& t) { return t; }
  inline static T convertBack(const T& t) { return t; }
};

template <>
struct KindValueToTableValueMapping<bool> {
  typedef uint64_t table_value_type;
  inline static uint64_t convert(const bool& t) { return t; }
  inline static bool convertBack(const uint64_t& t) { return t; }
};

template <class T>
struct KindValueToTableValueMapping<T*> {
  typedef void* table_value_type;
  inline static void* convert(const T*& t) {
    return reinterpret_cast<void*>(t);
  }
  inline static T* convertBack(void*& t) {
    return reinterpret_cast<T*>(t);
  }
};

template <class T>
struct KindValueToTableValueMapping<const T*> {
  typedef void* table_value_type;
  inline static void* convert(const T* const& t) {
    return reinterpret_cast<void*>(const_cast<T*>(t));
  }
  inline static const T* convertBack(const void* const& t) {
    return reinterpret_cast<const T*>(t);
  }
};

template <class AttrKind, class T>
struct OwnTable;

template <class AttrKind, class T>
struct KindValueToTableValueMapping<OwnTable<AttrKind, T> > {
  typedef typename KindValueToTableValueMapping<T>::table_value_type table_value_type;
};

template <class AttrKind>
struct KindTableMapping {
  typedef typename AttrKind::value_type table_identifier;
};

// ATTRIBUTE HASH TABLES =======================================================

// use a TAG to indicate which table it should be in
template <class value_type>
struct AttrHash : public __gnu_cxx::hash_map<std::pair<uint64_t, SoftNode>, value_type, AttrHashFcn> {};

template <>
class AttrHash<bool> : protected __gnu_cxx::hash_map<SoftNode, uint64_t, AttrHashBoolFcn> {

  typedef __gnu_cxx::hash_map<SoftNode, uint64_t, AttrHashBoolFcn> super;

  class BitAccessor {

    uint64_t& d_word;

    unsigned d_bit;

  public:

    BitAccessor(uint64_t& word, unsigned bit) :
      d_word(word),
      d_bit(bit) {
    }

    BitAccessor& operator=(bool b) {
      if(b) {
        // set the bit
        d_word |= (1 << d_bit);
      } else {
        // clear the bit
        d_word &= ~(1 << d_bit);
      }

      return *this;
    }

    operator bool() const {
      return (d_word & (1 << d_bit)) ? true : false;
    }
  };

  class BitIterator {

    std::pair<const SoftNode, uint64_t>* d_entry;

    unsigned d_bit;

  public:

    BitIterator() :
      d_entry(NULL),
      d_bit(0) {
    }

    BitIterator(std::pair<const SoftNode, uint64_t>& entry, unsigned bit) :
      d_entry(&entry),
      d_bit(bit) {
    }

    std::pair<const SoftNode, BitAccessor> operator*() {
      return std::make_pair(d_entry->first, BitAccessor(d_entry->second, d_bit));
    }

    bool operator==(const BitIterator& b) {
      return d_entry == b.d_entry && d_bit == b.d_bit;
    }
  };

  class ConstBitIterator {

    const std::pair<const SoftNode, uint64_t>* d_entry;

    unsigned d_bit;

  public:

    ConstBitIterator() :
      d_entry(NULL),
      d_bit(0) {
    }

    ConstBitIterator(const std::pair<const SoftNode, uint64_t>& entry, unsigned bit) :
      d_entry(&entry),
      d_bit(bit) {
    }

    std::pair<const SoftNode, bool> operator*() {
      return std::make_pair(d_entry->first, (d_entry->second & (1 << d_bit)) ? true : false);
    }

    bool operator==(const ConstBitIterator& b) {
      return d_entry == b.d_entry && d_bit == b.d_bit;
    }
  };

public:

  typedef std::pair<uint64_t, SoftNode> key_type;
  typedef bool data_type;
  typedef std::pair<const key_type, data_type> value_type;

  typedef BitIterator iterator;
  typedef ConstBitIterator const_iterator;

  BitIterator find(const std::pair<uint64_t, SoftNode>& k) {
    super::iterator i = super::find(k.second);
    if(i == super::end()) {
      return BitIterator();
    }
    Debug.printf("boolattr",
                 "underlying word at 0x%p looks like 0x%016llx, bit is %u\n",
                 &(*i).second,
                 (unsigned long long)((*i).second),
                 unsigned(k.first));
    return BitIterator(*i, k.first);
  }

  BitIterator end() {
    return BitIterator();
  }

  ConstBitIterator find(const std::pair<uint64_t, SoftNode>& k) const {
    super::const_iterator i = super::find(k.second);
    if(i == super::end()) {
      return ConstBitIterator();
    }
    Debug.printf("boolattr",
                 "underlying word at 0x%p looks like 0x%016llx, bit is %u\n",
                 &(*i).second,
                 (unsigned long long)((*i).second),
                 unsigned(k.first));
    return ConstBitIterator(*i, k.first);
  }

  ConstBitIterator end() const {
    return ConstBitIterator();
  }

  BitAccessor operator[](const std::pair<uint64_t, SoftNode>& k) {
    uint64_t& word = super::operator[](k.second);
    return BitAccessor(word, k.first);
  }
};/* class AttrHash<bool> */

// ATTRIBUTE PATTERN ===========================================================

/**
 * An "attribute type" structure.
 */
template <class T, class value_t>
struct Attribute {

  /** the value type for this attribute */
  typedef value_t value_type;

  /** cleanup routine when the Node goes away */
  static inline void cleanup(const value_t&) {}

  static inline uint64_t getId() { return s_id; }
  static inline uint64_t getHashValue() { return s_hashValue; }

  static const bool has_default_value = false;

private:

  /** an id */
  static const uint64_t s_id;

  /** an extra hash value (to avoid same-value-type collisions) */
  static const uint64_t s_hashValue;
};

/**
 * An "attribute type" structure for boolean flags (special).
 */
template <class T>
struct Attribute<T, bool> {

  /** the value type for this attribute */
  typedef bool value_type;

  /** cleanup routine when the Node goes away */
  static inline void cleanup(const bool&) {}

  static inline uint64_t getId() { return s_id; }
  static inline uint64_t getHashValue() { return s_hashValue; }

  static const bool has_default_value = true;
  static const bool default_value = false;

  static inline uint64_t checkID(uint64_t id) {
    AlwaysAssert(id <= 63,
                 "Too many boolean node attributes registered during initialization !");
    return id;
  }

private:

  /** a bit assignment */
  static const uint64_t s_id;

  /** an extra hash value (to avoid same-value-type collisions) */
  static const uint64_t s_hashValue;
};

// SPECIFIC, GLOBAL ATTRIBUTE DEFINITIONS ======================================

namespace attr {
  struct VarName {};
  struct Type {};

  template <class T>
  struct LastAttributeId {
    static uint64_t s_id;
  };

  template <class T>
  uint64_t LastAttributeId<T>::s_id = 0;
}/* CVC4::expr::attr namespace */

typedef Attribute<attr::VarName, std::string> VarNameAttr;
typedef Attribute<attr::Type, const CVC4::Type*> TypeAttr;

// ATTRIBUTE IDENTIFIER ASSIGNMENT =============================================

template <class T, class value_t>
const uint64_t Attribute<T, value_t>::s_id =
  attr::LastAttributeId<typename KindValueToTableValueMapping<value_t>::table_value_type>::s_id++;
template <class T, class value_t>
const uint64_t Attribute<T, value_t>::s_hashValue = Attribute<T, value_t>::s_id;

template <class T>
const uint64_t Attribute<T, bool>::s_id =
  Attribute<T, bool>::checkID(attr::LastAttributeId<bool>::s_id++);
template <class T>
const uint64_t Attribute<T, bool>::s_hashValue = Attribute<T, bool>::s_id;

class AttributeManager;

template <class T>
struct getTable {
  //inline AttrHash<KindTableValueMapping<T> >& get(AttributeManager& am);
};

// ATTRIBUTE MANAGER ===========================================================

class AttributeManager {
  NodeManager* d_nm;

  AttrHash<bool>    d_bools;
  AttrHash<uint64_t>    d_ints;
  AttrHash<SoftNode>    d_exprs;
  AttrHash<std::string> d_strings;
  AttrHash<void*>       d_ptrs;

  template <class T>
  friend struct getTable;

public:
  AttributeManager(NodeManager* nm) : d_nm(nm) {}

  template <class AttrKind>
  typename AttrKind::value_type getAttribute(const Node& n,
                                             const AttrKind&) const;

  template <class AttrKind>
  bool hasAttribute(const Node& n,
                    const AttrKind&) const;

  template <class AttrKind>
  bool hasAttribute(const Node& n,
                    const AttrKind&,
                    typename AttrKind::value_type*) const;

  template <class AttrKind>
  void setAttribute(const Node& n,
                    const AttrKind&,
                    const typename AttrKind::value_type& value);
};

// MAPPING OF ATTRIBUTE KINDS TO TABLES IN THE ATTRIBUTE MANAGER ===============

template <>
struct getTable<bool> {
  typedef AttrHash<bool> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_bools;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_bools;
  }
};

template <>
struct getTable<uint64_t> {
  typedef AttrHash<uint64_t> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_ints;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_ints;
  }
};

template <>
struct getTable<Node> {
  typedef AttrHash<SoftNode> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_exprs;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_exprs;
  }
};

template <>
struct getTable<std::string> {
  typedef AttrHash<std::string> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_strings;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_strings;
  }
};

template <class T>
struct getTable<const T*> {
  typedef AttrHash<void*> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_ptrs;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_ptrs;
  }
};

// ATTRIBUTE MANAGER IMPLEMENTATIONS ===========================================

template <class AttrKind>
typename AttrKind::value_type AttributeManager::getAttribute(const Node& n,
                                                             const AttrKind&) const {

  typedef typename AttrKind::value_type value_type;
  typedef KindValueToTableValueMapping<value_type> mapping;
  typedef typename getTable<value_type>::table_type table_type;

  const table_type& ah = getTable<value_type>::get(*this);
  typename table_type::const_iterator i = ah.find(std::make_pair(AttrKind::getId(), n));

  if(i == ah.end()) {
    return typename AttrKind::value_type();
  }

  return mapping::convertBack((*i).second);
}

/* helper template class for hasAttribute(), specialized based on
 * whether AttrKind has a "default value" that all Nodes implicitly
 * have or not. */
template <bool has_default, class AttrKind>
struct HasAttribute;

template <class AttrKind>
struct HasAttribute<true, AttrKind> {
  static inline bool hasAttribute(const AttributeManager* am,
                                  const Node& n) {
    return true;
  }

  static inline bool hasAttribute(const AttributeManager* am,
                                  const Node& n,
                                  typename AttrKind::value_type* ret) {
    if(ret != NULL) {
      typedef typename AttrKind::value_type value_type;
      typedef KindValueToTableValueMapping<value_type> mapping;
      typedef typename getTable<value_type>::table_type table_type;

      const table_type& ah = getTable<value_type>::get(*am);
      typename table_type::const_iterator i = ah.find(std::make_pair(AttrKind::getId(), n));

      if(i == ah.end()) {
        *ret = AttrKind::default_value;
      } else {
        *ret = mapping::convertBack((*i).second);
      }
    }

    return true;
  }
};

template <class AttrKind>
struct HasAttribute<false, AttrKind> {
  static inline bool hasAttribute(const AttributeManager* am,
                                  const Node& n) {
    typedef typename AttrKind::value_type value_type;
    typedef KindValueToTableValueMapping<value_type> mapping;
    typedef typename getTable<value_type>::table_type table_type;

    const table_type& ah = getTable<value_type>::get(*am);
    typename table_type::const_iterator i = ah.find(std::make_pair(AttrKind::getId(), n));

    if(i == ah.end()) {
      return false;
    }

    return true;
  }

  static inline bool hasAttribute(const AttributeManager* am,
                                  const Node& n,
                                  typename AttrKind::value_type* ret) {
    typedef typename AttrKind::value_type value_type;
    typedef KindValueToTableValueMapping<value_type> mapping;
    typedef typename getTable<value_type>::table_type table_type;

    const table_type& ah = getTable<value_type>::get(*am);
    typename table_type::const_iterator i = ah.find(std::make_pair(AttrKind::getId(), n));

    if(i == ah.end()) {
      return false;
    }

    if(ret != NULL) {
      *ret = mapping::convertBack((*i).second);
    }

    return true;
  }
};

template <class AttrKind>
bool AttributeManager::hasAttribute(const Node& n,
                                    const AttrKind&) const {
  return HasAttribute<AttrKind::has_default_value, AttrKind>::hasAttribute(this, n);
}

template <class AttrKind>
bool AttributeManager::hasAttribute(const Node& n,
                                    const AttrKind&,
                                    typename AttrKind::value_type* ret) const {
  return HasAttribute<AttrKind::has_default_value, AttrKind>::hasAttribute(this, n, ret);
}

template <class AttrKind>
inline void AttributeManager::setAttribute(const Node& n,
                                           const AttrKind&,
                                           const typename AttrKind::value_type& value) {

  typedef typename AttrKind::value_type value_type;
  typedef KindValueToTableValueMapping<value_type> mapping;
  typedef typename getTable<value_type>::table_type table_type;

  table_type& ah = getTable<value_type>::get(*this);
  ah[std::make_pair(AttrKind::getId(), n)] = mapping::convert(value);
}

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* __CVC4__EXPR__ATTRIBUTE_H */
