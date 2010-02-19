/*********************                                           -*- C++ -*-  */
/** attribute.h
 ** Original author: mdeters
 ** Major contributors: dejan
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
 ** struct VarName_attr {
 **
 **   // the value type for this attribute
 **   typedef std::string value_type;
 **
 **   // an extra hash value (to avoid same-value-type collisions)
 **   enum { hash_value = 1 };
 **
 **   // whether inclusion in the table keeps the (key) Node live or not
 **   static const bool hard_key = false;
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

struct AttrHashFcn {
  enum { LARGE_PRIME = 1 };
  std::size_t operator()(const std::pair<unsigned, SoftNode>& p) const {
    return p.first * LARGE_PRIME + p.second.hash();
  }
};

struct AttrHashBoolFcn {
  std::size_t operator()(const SoftNode& n) const {
    return n.hash();
  }
};

/*
template <class T>
class AttrTable;

template <>
class AttrTable<bool> {
public:
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
  };

  // bool specialization
  //static AttrHash<uint64_t>* s_hash;

  //typedef AttrHash<SoftNode, uint64_t>::iterator iterator;
  //typedef AttrHash<SoftNode, uint64_t>::const_iterator const_iterator;

  template <class Attr>
  BitAccessor& find(Node e, const Attr&);

  template <class Attr>
  bool find(Node e, const Attr&) const;
};

template <>
class AttrTable<uint64_t> {
public:  
  // int(egral) specialization
  //static AttrHash<uint64_t>* s_hash;
  typedef AttrHash<uint64_t>::iterator iterator;
  typedef AttrHash<uint64_t>::const_iterator const_iterator;
  uint64_t& find(TNode);
};

template <class T>
class AttrTable<T*> {
public:
  // pointer specialization
  //static AttrHash<void*>* s_hash;
  typedef AttrHash<void*>::iterator iterator;
  typedef AttrHash<void*>::const_iterator const_iterator;
};

template <>
class AttrTable<Node> {
public:
  // Node specialization
  //static AttrHash<SoftNode>* s_hash;
  typedef AttrHash<SoftNode>::iterator iterator;
  typedef AttrHash<SoftNode>::const_iterator const_iterator;
  Node find(TNode);
};

template <>
class AttrTable<std::string> {
public:
  // string specialization
  //static AttrHash<std::string>* s_hash;
  typedef AttrHash<std::string>::iterator iterator;
  typedef AttrHash<std::string>::const_iterator const_iterator;
  Node find(TNode);
};

*/

/*
template <class T>
AttrHash<void*>*    AttrTable<T*>::s_hash       = &g_hash_ptr;
*/

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
  inline static const T* convertBack(const void*& t) {
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

// use a TAG to indicate which table it should be in
template <class value_type>
struct AttrHash : public __gnu_cxx::hash_map<std::pair<unsigned, SoftNode>, value_type, AttrHashFcn> {};

/*
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
  };

  class BitIterator {

    std::pair<SoftNode, uint64_t>& d_word;

    int d_bit;

  public:

    BitIterator() :
      d_word((uint64_t&) d_bit),
      d_bit(-1) {
    }

    BitIterator(std::pair<SoftNode, uint64_t>& entry, unsigned bit) :
      d_entry(entry),
      d_bit(bit) {
    }

    BitAccessor operator*() {
      return BitAccessor(d_word, d_bit);
    }
  };

  class ConstBitIterator {

    uint64_t& d_word;

    unsigned d_bit;

  public:

    ConstBitIterator(uint64_t& word, unsigned bit) :
      d_word(word),
      d_bit(bit) {
    }

    bool operator*() {
      return (d_word & (1 << d_bit)) ? true : false;
    }
  };

public:

  typedef std::pair<unsigned, SoftNode> key_type;
  typedef bool data_type;
  typedef std::pair<const key_type, data_type> value_type;

  typedef BitIterator iterator;
  typedef ConstBitIterator const_iterator;

  BitIterator find(const std::pair<unsigned, SoftNode>& k) {
    super::iterator i = super::find(k.second);
    if(i == super::end()) {
      return BitIterator();
    }
    return BitIterator(*i, k.first);
  }

  ConstBitIterator find(const std::pair<unsigned, SoftNode>& k) const {
    super::const_iterator i = super::find(k.second);
    return ConstBitIterator(*i, k.first);
  }

  BitAccessor operator[](const std::pair<unsigned, SoftNode>& k) {
    uint64_t& word = super::operator[](k.second);
    return BitAccessor(word, k.first);
  }
};
*/

/**
 * An "attribute type" structure.
 */
template <class T, class value_t>
struct Attribute {

  /** the value type for this attribute */
  typedef value_t value_type;

  /** cleanup routine when the Node goes away */
  static inline void cleanup(const value_t&) {}

  static inline unsigned getId() { return s_id; }
  static inline unsigned getHashValue() { return s_hashValue; }

private:

  /** an id */
  static unsigned s_id;

  /** an extra hash value (to avoid same-value-type collisions) */
  static unsigned s_hashValue;
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

  static inline unsigned getId() { return s_id; }
  static inline unsigned getBit() { return s_bit; }
  static inline unsigned getHashValue() { return s_hashValue; }

private:

  /** an id */
  static unsigned s_id;

  /** a bit assignment */
  static unsigned s_bit;

  /** an extra hash value (to avoid same-value-type collisions) */
  static unsigned s_hashValue;
};

namespace attr {
  struct VarName {};
  struct Type {};

  template <class T>
  struct LastAttributeId {
    static unsigned s_id;
  };

  template <class T>
  unsigned LastAttributeId<T>::s_id = 0;

  struct BitAssignment {
    static unsigned s_bit;
  };
}/* CVC4::expr::attr namespace */

typedef Attribute<attr::VarName, std::string> VarNameAttr;
typedef Attribute<attr::Type, const CVC4::Type*> TypeAttr;

/*
template <class Attr>
class AttributeTable {
  typedef typename Attr::value_type value_type;

  AttrTable<value_type>& d_table;
  
};
*/

/*
template <class T>
struct AttrTables {
  
};
*/

template <class T, class value_t>
unsigned Attribute<T, value_t>::s_id =
  attr::LastAttributeId<typename KindValueToTableValueMapping<value_t>::table_value_type>::s_id++;
template <class T, class value_t>
unsigned Attribute<T, value_t>::s_hashValue = Attribute<T, value_t>::s_id;

template <class T>
unsigned Attribute<T, bool>::s_id =
  attr::LastAttributeId<bool>::s_id++;
template <class T>
unsigned Attribute<T, bool>::s_bit =
  attr::BitAssignment::s_bit++;
template <class T>
unsigned Attribute<T, bool>::s_hashValue = Attribute<T, bool>::s_id;

class AttributeManager;

template <class T>
struct getTable {
  //inline AttrHash<KindTableValueMapping<T> >& get(AttributeManager& am);
};

class AttributeManager {
  NodeManager* d_nm;

  AttrHash<uint64_t>    d_bools;
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
                                             const AttrKind&);

  template <class AttrKind>
  bool hasAttribute(const Node& n,
                    const AttrKind&,
                    typename AttrKind::value_type* = NULL);

  template <class AttrKind>
  void setAttribute(const Node& n,
                    const AttrKind&,
                    const typename AttrKind::value_type& value);
};

template <>
struct getTable<bool> {
  typedef AttrHash<uint64_t> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_bools;
  }
};

template <>
struct getTable<uint64_t> {
  typedef AttrHash<uint64_t> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_ints;
  }
};

template <>
struct getTable<Node> {
  typedef AttrHash<SoftNode> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_exprs;
  }
};

template <>
struct getTable<std::string> {
  typedef AttrHash<std::string> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_strings;
  }
};

template <class T>
struct getTable<T*> {
  typedef AttrHash<void*> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_ptrs;
  }
};

template <class AttrKind>
typename AttrKind::value_type AttributeManager::getAttribute(const Node& n,
                                                             const AttrKind& marker) {

  typedef typename AttrKind::value_type value_type;
  typedef KindValueToTableValueMapping<value_type> mapping;
  typedef typename getTable<value_type>::table_type table_type;

  table_type& ah = getTable<value_type>::get(*this);
  typename table_type::iterator i = ah.find(std::make_pair(AttrKind::getId(), n));

  if(i == ah.end()) {
    return typename AttrKind::value_type();
  }

  return mapping::convertBack(i->second);
}

template <class AttrKind>
bool AttributeManager::hasAttribute(const Node& n,
                                    const AttrKind&,
                                    typename AttrKind::value_type* ret) {

  typedef typename AttrKind::value_type value_type;
  typedef KindValueToTableValueMapping<value_type> mapping;
  typedef typename getTable<value_type>::table_type table_type;

  table_type& ah = getTable<value_type>::get(*this);
  typename table_type::iterator i = ah.find(std::make_pair(AttrKind::getId(), n));

  if(i == ah.end()) {
    return false;
  }

  if(ret != NULL) {
    *ret = mapping::convertBack(i->second);
  }

  return true;
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

/*

template <class attr>
struct last_attribute_id {
  static unsigned value;
};

template <class attr>
unsigned last_attribute_id<attr>::value = 0;

template <class attr>
unsigned register_attribute_kind() {
  return last_attribute_id<attr>::value++;
}

*/

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* __CVC4__EXPR__ATTRIBUTE_H */
