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
#include "expr/node.h"
#include "expr/type.h"

#include "util/output.h"

namespace CVC4 {
namespace expr {

// ATTRIBUTE HASH FUNCTIONS ====================================================

namespace attr {

/**
 * A hash function for attribute table keys.  Attribute table keys are
 * pairs, (unique-attribute-id, Node).
 */
struct AttrHashFcn {
  enum { LARGE_PRIME = 32452843ul };
  std::size_t operator()(const std::pair<uint64_t, NodeValue*>& p) const {
    return p.first * LARGE_PRIME + p.second->hash();
  }
};

/**
 * A hash function for boolean-valued attribute table keys; here we
 * don't have to store a pair as the key, because we use a known bit
 * in [0..63] for each attribute
 */
struct AttrHashBoolFcn {
  std::size_t operator()(NodeValue* nv) const {
    return nv->hash();
  }
};

}/* CVC4::expr::attr namespace */

// ATTRIBUTE TYPE MAPPINGS =====================================================

namespace attr {

/**
 * KindValueToTableValueMapping is a compile-time-only mechanism to
 * convert "attribute value types" into "table value types" and back
 * again.
 *
 * Each instantiation <T> is expected to have three members:
 *
 *   typename table_value_type
 *
 *      A type representing the underlying table's value_type for
 *      attribute value type (T).  It may be different from T, e.g. T
 *      could be a pointer-to-Foo, but the underlying table value_type
 *      might be pointer-to-void.
 *
 *   static [convertible-to-table_value_type] convert([convertible-from-T])
 *
 *      Converts a T into a table_value_type.  Used to convert an
 *      attribute value on setting it (and assigning it into the
 *      underlying table).  See notes on specializations of
 *      KindValueToTableValueMapping, below.
 *
 *   static [convertible-to-T] convertBack([convertible-from-table_value_type])
 *
 *      Converts a table_value_type back into a T.  Used to convert an
 *      underlying table value back into the attribute's expected type
 *      when retrieving it from the table.  See notes on
 *      specializations of KindValueToTableValueMapping, below.
 *
 * This general (non-specialized) implementation of the template does
 * nothing.
 */
template <class T>
struct KindValueToTableValueMapping {
  /** Simple case: T == table_value_type */
  typedef T table_value_type;
  /** No conversion necessary */
  inline static T convert(const T& t) { return t; }
  /** No conversion necessary */
  inline static T convertBack(const T& t) { return t; }
};

/**
 * Specialization of KindValueToTableValueMapping<> for pointer-valued
 * attributes.
 */
template <class T>
struct KindValueToTableValueMapping<T*> {
  /** Table's value type is void* */
  typedef void* table_value_type;
  /** A simple reinterpret_cast<>() conversion from T* to void* */
  inline static void* convert(const T* const& t) {
    return reinterpret_cast<void*>(const_cast<T*>(t));
  }
  /** A simple reinterpret_cast<>() conversion from void* to T* */
  inline static T* convertBack(void* const& t) {
    return reinterpret_cast<T*>(t);
  }
};

/**
 * Specialization of KindValueToTableValueMapping<> for const
 * pointer-valued attributes.
 */
template <class T>
struct KindValueToTableValueMapping<const T*> {
  /** Table's value type is void* */
  typedef void* table_value_type;
  /** A simple reinterpret_cast<>() conversion from const T* const to void* */
  inline static void* convert(const T* const& t) {
    return reinterpret_cast<void*>(const_cast<T*>(t));
  }
  /** A simple reinterpret_cast<>() conversion from const void* const to T* */
  inline static const T* convertBack(const void* const& t) {
    return reinterpret_cast<const T*>(t);
  }
};

}/* CVC4::expr::attr namespace */

// ATTRIBUTE HASH TABLES =======================================================

namespace attr {

/**
 * An "AttrHash<value_type>"---the hash table underlying
 * attributes---is simply a mapping of pair<unique-attribute-id, Node>
 * to value_type using our specialized hash function for these pairs.
 */
template <class value_type>
struct AttrHash :
    public __gnu_cxx::hash_map<std::pair<uint64_t, NodeValue*>,
                               value_type,
                               AttrHashFcn> {
};

/**
 * In the case of Boolean-valued attributes we have a special
 * "AttrHash<bool>" to pack bits together in words.
 */
template <>
class AttrHash<bool> :
    protected __gnu_cxx::hash_map<NodeValue*,
                                  uint64_t,
                                  AttrHashBoolFcn> {

  /** A "super" type, like in Java, for easy reference below. */
  typedef __gnu_cxx::hash_map<NodeValue*, uint64_t, AttrHashBoolFcn> super;

  /**
   * BitAccessor allows us to return a bit "by reference."  Of course,
   * we don't require bit-addressibility supported by the system, we
   * do it with a complex type.
   */
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

  /**
   * A (somewhat degenerate) iterator over boolean-valued attributes.
   * This iterator doesn't support anything except comparison and
   * dereference.  It's intended just for the result of find() on the
   * table.
   */
  class BitIterator {

    std::pair<NodeValue* const, uint64_t>* d_entry;

    unsigned d_bit;

  public:

    BitIterator() :
      d_entry(NULL),
      d_bit(0) {
    }

    BitIterator(std::pair<NodeValue* const, uint64_t>& entry, unsigned bit) :
      d_entry(&entry),
      d_bit(bit) {
    }

    std::pair<NodeValue* const, BitAccessor> operator*() {
      return std::make_pair(d_entry->first, BitAccessor(d_entry->second, d_bit));
    }

    bool operator==(const BitIterator& b) {
      return d_entry == b.d_entry && d_bit == b.d_bit;
    }
  };

  /**
   * A (somewhat degenerate) const_iterator over boolean-valued
   * attributes.  This const_iterator doesn't support anything except
   * comparison and dereference.  It's intended just for the result of
   * find() on the table.
   */
  class ConstBitIterator {

    const std::pair<NodeValue* const, uint64_t>* d_entry;

    unsigned d_bit;

  public:

    ConstBitIterator() :
      d_entry(NULL),
      d_bit(0) {
    }

    ConstBitIterator(const std::pair<NodeValue* const, uint64_t>& entry, unsigned bit) :
      d_entry(&entry),
      d_bit(bit) {
    }

    std::pair<NodeValue* const, bool> operator*() {
      return std::make_pair(d_entry->first, (d_entry->second & (1 << d_bit)) ? true : false);
    }

    bool operator==(const ConstBitIterator& b) {
      return d_entry == b.d_entry && d_bit == b.d_bit;
    }
  };

public:

  typedef std::pair<uint64_t, NodeValue*> key_type;
  typedef bool data_type;
  typedef std::pair<const key_type, data_type> value_type;

  /** an iterator type; see above for limitations */
  typedef BitIterator iterator;
  /** a const_iterator type; see above for limitations */
  typedef ConstBitIterator const_iterator;

  /**
   * Find the boolean value in the hash table.  Returns something ==
   * end() if not found.
   */
  BitIterator find(const std::pair<uint64_t, NodeValue*>& k) {
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

  /** The "off the end" iterator */
  BitIterator end() {
    return BitIterator();
  }

  /**
   * Find the boolean value in the hash table.  Returns something ==
   * end() if not found.
   */
  ConstBitIterator find(const std::pair<uint64_t, NodeValue*>& k) const {
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

  /** The "off the end" const_iterator */
  ConstBitIterator end() const {
    return ConstBitIterator();
  }

  /**
   * Access the hash table using the underlying operator[].  Inserts
   * the key into the table (associated to default value) if it's not
   * already there.
   */
  BitAccessor operator[](const std::pair<uint64_t, NodeValue*>& k) {
    uint64_t& word = super::operator[](k.second);
    return BitAccessor(word, k.first);
  }
};/* class AttrHash<bool> */

}/* CVC4::expr::attr namespace */

// ATTRIBUTE CLEANUP FUNCTIONS =================================================

namespace attr {

/** Default cleanup for unmanaged Attribute<> */
template <class T>
struct AttributeCleanupFcn {
  inline void cleanup(const T&) {}
};

/** Default cleanup for ManagedAttribute<> */
template <class T>
struct ManagedAttributeCleanupFcn {
};

/** Specialization for T* */
template <class T>
struct ManagedAttributeCleanupFcn<T*> {
  inline void cleanup(T* p) { delete p; }
};

/** Specialization for const T* */
template <class T>
struct ManagedAttributeCleanupFcn<const T*> {
  inline void cleanup(const T* p) { delete p; }
};

}/* CVC4::expr::attr namespace */

// ATTRIBUTE DEFINITION ========================================================

/**
 * An "attribute type" structure.
 *
 * @param T the tag for the attribute kind.
 *
 * @param value_t the underlying value_type for the attribute kind
 *
 * @param CleanupFcn Clean-up routine for associated values when the
 * Node goes away.  Useful, e.g., for pointer-valued attributes when
 * the values are "owned" by the table.
 *
 * @param context_dependent whether this attribute kind is
 * context-dependent
 */
template <class T,
          class value_t,
          class CleanupFcn = attr::AttributeCleanupFcn<value_t>,
          bool context_dependent = false>
struct Attribute {

  /** The value type for this attribute. */
  typedef value_t value_type;

  /** Get the unique ID associated to this attribute. */
  static inline uint64_t getId() { return s_id; }

  /**
   * This attribute does not have a default value: calling
   * hasAttribute() for a Node that hasn't had this attribute set will
   * return false, and getAttribute() for the Node will return a
   * default-constructed value_type.
   */
  static const bool has_default_value = false;

private:

  /**
   * The unique ID associated to this attribute.  Assigned statically,
   * at load time.
   */
  static const uint64_t s_id;
};

/**
 * An "attribute type" structure for boolean flags (special).
 */
template <class T, class CleanupFcn, bool context_dependent>
struct Attribute<T, bool, CleanupFcn, context_dependent> {

  /** The value type for this attribute; here, bool. */
  typedef bool value_type;

  /** Get the unique ID associated to this attribute. */
  static inline uint64_t getId() { return s_id; }

  /**
   * Such bool-valued attributes ("flags") have a default value: they
   * are false for all nodes on entry.  Calling hasAttribute() for a
   * Node that hasn't had this attribute set will return true, and
   * getAttribute() for the Node will return the default_value below.
   */
  static const bool has_default_value = true;

  /**
   * Default value of the attribute for Nodes without one explicitly
   * set.
   */
  static const bool default_value = false;

  /**
   * Check that the ID is a valid ID for bool-valued attributes.  Fail
   * an assert if not.  Otherwise return the id.
   */
  static inline uint64_t checkID(uint64_t id) {
    AlwaysAssert( id <= 63,
                  "Too many boolean node attributes registered "
                  "during initialization !" );
    return id;
  }

private:

  /** IDs for bool-valued attributes are actually bit assignments. */
  static const uint64_t s_id;
};

// FIXME make context-dependent
template <class T,
          class value_type>
struct CDAttribute :
    public Attribute<T, value_type, attr::AttributeCleanupFcn<value_type>, true> {};

// FIXME make context-dependent
template <class T,
          class value_type,
          class CleanupFcn = attr::ManagedAttributeCleanupFcn<value_type> >
struct ManagedAttribute :
    public Attribute<T, value_type, CleanupFcn, false> {};

// ATTRIBUTE IDENTIFIER ASSIGNMENT =============================================

namespace attr {

/**
 * This is the last-attribute-assigner.  IDs are not globally
 * unique; rather, they are unique for each table_value_type.
 */
template <class T>
struct LastAttributeId {
  static uint64_t s_id;
};

/** Initially zero. */
template <class T>
uint64_t LastAttributeId<T>::s_id = 0;

}/* CVC4::expr::attr namespace */

/** Assign unique IDs to attributes at load time. */
template <class T, class value_t, class CleanupFcn, bool context_dependent>
const uint64_t Attribute<T, value_t, CleanupFcn, context_dependent>::s_id =
  attr::LastAttributeId<typename attr::KindValueToTableValueMapping<value_t>::table_value_type>::s_id++;

/**
 * Assign unique IDs to bool-valued attributes at load time, checking
 * that they are in range.
 */
template <class T, class CleanupFcn, bool context_dependent>
const uint64_t Attribute<T, bool, CleanupFcn, context_dependent>::s_id =
  Attribute<T, bool, CleanupFcn, context_dependent>::checkID(attr::LastAttributeId<bool>::s_id++);

// ATTRIBUTE MANAGER ===========================================================

namespace attr {

/**
 * A container for the main attribute tables of the system.  There's a
 * one-to-one NodeManager : AttributeManager correspondence.
 */
class AttributeManager {

  /** Underlying hash table for boolean-valued attributes */
  AttrHash<bool>        d_bools;
  /** Underlying hash table for integral-valued attributes */
  AttrHash<uint64_t>    d_ints;
  /** Underlying hash table for node-valued attributes */
  AttrHash<TNode>       d_exprs;
  /** Underlying hash table for string-valued attributes */
  AttrHash<std::string> d_strings;
  /** Underlying hash table for pointer-valued attributes */
  AttrHash<void*>       d_ptrs;

  /**
   * getTable<> is a helper template that gets the right table from an
   * AttributeManager given its type.
   */
  template <class T>
  friend struct getTable;

public:

  /** Construct an attribute manager. */
  AttributeManager() {}

  /**
   * Get a particular attribute on a particular node.
   *
   * @param n the node about which to inquire
   *
   * @param const AttrKind& the attribute kind to get
   *
   * @return the attribute value, if set, or a default-constructed
   * AttrKind::value_type if not.
   */
  template <class AttrKind>
  typename AttrKind::value_type getAttribute(TNode n,
                                             const AttrKind&) const;

  // Note that there are two, distinct hasAttribute() declarations for
  // a reason (rather than using a default argument): they permit more
  // optimized code.  The first (without parameter "ret") need never
  // check whether its parameter is NULL.

  /**
   * Determine if a particular attribute exists for a particular node.
   *
   * @param n the node about which to inquire
   *
   * @param const AttrKind& the attribute kind to inquire about
   *
   * @return true if the given node has the given attribute
   */
  template <class AttrKind>
  bool hasAttribute(TNode n,
                    const AttrKind&) const;

  /**
   * Determine if a particular attribute exists for a particular node,
   * and get it if it does.
   *
   * @param n the node about which to inquire
   *
   * @param const AttrKind& the attribute kind to inquire about
   *
   * @param ret a pointer to a return value, set in case the node has
   * the attribute
   *
   * @return true if the given node has the given attribute
   */
  template <class AttrKind>
  bool hasAttribute(TNode n,
                    const AttrKind&,
                    typename AttrKind::value_type& ret) const;

  /**
   * Set a particular attribute on a particular node.
   *
   * @param n the node for which to set the attribute
   *
   * @param const AttrKind& the attribute kind to set
   *
   * @param ret a pointer to a return value, set in case the node has
   * the attribute
   *
   * @return true if the given node has the given attribute
   */
  template <class AttrKind>
  void setAttribute(TNode n,
                    const AttrKind&,
                    const typename AttrKind::value_type& value);
};

}/* CVC4::expr::attr namespace */

// MAPPING OF ATTRIBUTE KINDS TO TABLES IN THE ATTRIBUTE MANAGER ===============

namespace attr {

/**
 * The getTable<> template provides (static) access to the
 * AttributeManager field holding the table.
 */
template <class T>
struct getTable;

/** Access the "d_bools" member of AttributeManager. */
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

/** Access the "d_ints" member of AttributeManager. */
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

/** Access the "d_exprs" member of AttributeManager. */
template <>
struct getTable<Node> {
  typedef AttrHash<TNode> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_exprs;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_exprs;
  }
};

/** Access the "d_strings" member of AttributeManager. */
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

/** Access the "d_ptrs" member of AttributeManager. */
template <class T>
struct getTable<T*> {
  typedef AttrHash<void*> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_ptrs;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_ptrs;
  }
};

/** Access the "d_ptrs" member of AttributeManager. */
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

}/* CVC4::expr::attr namespace */

// ATTRIBUTE MANAGER IMPLEMENTATIONS ===========================================

namespace attr {

// implementation for AttributeManager::getAttribute()
template <class AttrKind>
typename AttrKind::value_type AttributeManager::getAttribute(TNode n,
                                                             const AttrKind&) const {

  typedef typename AttrKind::value_type value_type;
  typedef KindValueToTableValueMapping<value_type> mapping;
  typedef typename getTable<value_type>::table_type table_type;

  const table_type& ah = getTable<value_type>::get(*this);
  typename table_type::const_iterator i = ah.find(std::make_pair(AttrKind::getId(), n.d_nv));

  if(i == ah.end()) {
    return typename AttrKind::value_type();
  }

  return mapping::convertBack((*i).second);
}

/* Helper template class for hasAttribute(), specialized based on
 * whether AttrKind has a "default value" that all Nodes implicitly
 * have or not. */
template <bool has_default, class AttrKind>
struct HasAttribute;

/**
 * Specialization of HasAttribute<> helper template for AttrKinds
 * with a default value.
 */
template <class AttrKind>
struct HasAttribute<true, AttrKind> {
  /** This implementation is simple; it's always true. */
  static inline bool hasAttribute(const AttributeManager* am,
                                  NodeValue* nv) {
    return true;
  }

  /**
   * This implementation returns the AttrKind's default value if the
   * Node doesn't have the given attribute.
   */
  static inline bool hasAttribute(const AttributeManager* am,
                                  NodeValue* nv,
                                  typename AttrKind::value_type& ret) {
    typedef typename AttrKind::value_type value_type;
    typedef KindValueToTableValueMapping<value_type> mapping;
    typedef typename getTable<value_type>::table_type table_type;

    const table_type& ah = getTable<value_type>::get(*am);
    typename table_type::const_iterator i = ah.find(std::make_pair(AttrKind::getId(), nv));

    if(i == ah.end()) {
      ret = AttrKind::default_value;
    } else {
      ret = mapping::convertBack((*i).second);
    }

    return true;
  }
};

/**
 * Specialization of HasAttribute<> helper template for AttrKinds
 * without a default value.
 */
template <class AttrKind>
struct HasAttribute<false, AttrKind> {
  static inline bool hasAttribute(const AttributeManager* am,
                                  NodeValue* nv) {
    typedef typename AttrKind::value_type value_type;
    typedef KindValueToTableValueMapping<value_type> mapping;
    typedef typename getTable<value_type>::table_type table_type;

    const table_type& ah = getTable<value_type>::get(*am);
    typename table_type::const_iterator i = ah.find(std::make_pair(AttrKind::getId(), nv));

    if(i == ah.end()) {
      return false;
    }

    return true;
  }

  static inline bool hasAttribute(const AttributeManager* am,
                                  NodeValue* nv,
                                  typename AttrKind::value_type& ret) {
    typedef typename AttrKind::value_type value_type;
    typedef KindValueToTableValueMapping<value_type> mapping;
    typedef typename getTable<value_type>::table_type table_type;

    const table_type& ah = getTable<value_type>::get(*am);
    typename table_type::const_iterator i = ah.find(std::make_pair(AttrKind::getId(), nv));

    if(i == ah.end()) {
      return false;
    }

    ret = mapping::convertBack((*i).second);

    return true;
  }
};

template <class AttrKind>
bool AttributeManager::hasAttribute(TNode n,
                                    const AttrKind&) const {
  return HasAttribute<AttrKind::has_default_value, AttrKind>::hasAttribute(this, n.d_nv);
}

template <class AttrKind>
bool AttributeManager::hasAttribute(TNode n,
                                    const AttrKind&,
                                    typename AttrKind::value_type& ret) const {
  return HasAttribute<AttrKind::has_default_value, AttrKind>::hasAttribute(this, n.d_nv, ret);
}

template <class AttrKind>
inline void AttributeManager::setAttribute(TNode n,
                                           const AttrKind&,
                                           const typename AttrKind::value_type& value) {

  typedef typename AttrKind::value_type value_type;
  typedef KindValueToTableValueMapping<value_type> mapping;
  typedef typename getTable<value_type>::table_type table_type;

  table_type& ah = getTable<value_type>::get(*this);
  ah[std::make_pair(AttrKind::getId(), n.d_nv)] = mapping::convert(value);
}

}/* CVC4::expr::attr namespace */
}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* __CVC4__EXPR__ATTRIBUTE_H */
