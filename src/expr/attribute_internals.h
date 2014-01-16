/*********************                                                        */
/*! \file attribute_internals.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Dejan Jovanovic, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Node attributes' internals.
 **
 ** Node attributes' internals.
 **/

#include "cvc4_private.h"

#ifndef CVC4_ATTRIBUTE_H__INCLUDING__ATTRIBUTE_INTERNALS_H
#  error expr/attribute_internals.h should only be included by expr/attribute.h
#endif /* CVC4_ATTRIBUTE_H__INCLUDING__ATTRIBUTE_INTERNALS_H */

#ifndef __CVC4__EXPR__ATTRIBUTE_INTERNALS_H
#define __CVC4__EXPR__ATTRIBUTE_INTERNALS_H

#include <ext/hash_map>

#include "context/cdhashmap.h"

namespace CVC4 {
namespace expr {

// ATTRIBUTE HASH FUNCTIONS ====================================================

namespace attr {

/**
 * A hash function for attribute table keys.  Attribute table keys are
 * pairs, (unique-attribute-id, Node).
 */
struct AttrHashFunction {
  enum { LARGE_PRIME = 32452843ul };
  std::size_t operator()(const std::pair<uint64_t, NodeValue*>& p) const {
    return p.first * LARGE_PRIME + p.second->getId();
  }
};/* struct AttrHashFunction */

/**
 * A hash function for boolean-valued attribute table keys; here we
 * don't have to store a pair as the key, because we use a known bit
 * in [0..63] for each attribute
 */
struct AttrBoolHashFunction {
  std::size_t operator()(NodeValue* nv) const {
    return (size_t)nv->getId();
  }
};/* struct AttrBoolHashFunction */

}/* CVC4::expr::attr namespace */

// ATTRIBUTE TYPE MAPPINGS =====================================================

namespace attr {

/**
 * KindValueToTableValueMapping is a compile-time-only mechanism to
 * convert "attribute value types" into "table value types" and back
 * again.
 *
 * Each instantiation < T > is expected to have three members:
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
class AttrHash :
    public __gnu_cxx::hash_map<std::pair<uint64_t, NodeValue*>,
                               value_type,
                               AttrHashFunction> {
};/* class AttrHash<> */

/**
 * In the case of Boolean-valued attributes we have a special
 * "AttrHash<bool>" to pack bits together in words.
 */
template <>
class AttrHash<bool> :
    protected __gnu_cxx::hash_map<NodeValue*,
                                  uint64_t,
                                  AttrBoolHashFunction> {

  /** A "super" type, like in Java, for easy reference below. */
  typedef __gnu_cxx::hash_map<NodeValue*, uint64_t, AttrBoolHashFunction> super;

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
  };/* class AttrHash<bool>::BitAccessor */

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
      return std::make_pair(d_entry->first,
                            BitAccessor(d_entry->second, d_bit));
    }

    bool operator==(const BitIterator& b) {
      return d_entry == b.d_entry && d_bit == b.d_bit;
    }
  };/* class AttrHash<bool>::BitIterator */

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

    ConstBitIterator(const std::pair<NodeValue* const, uint64_t>& entry,
                     unsigned bit) :
      d_entry(&entry),
      d_bit(bit) {
    }

    std::pair<NodeValue* const, bool> operator*() {
      return std::make_pair(d_entry->first,
                            (d_entry->second & (1 << d_bit)) ? true : false);
    }

    bool operator==(const ConstBitIterator& b) {
      return d_entry == b.d_entry && d_bit == b.d_bit;
    }
  };/* class AttrHash<bool>::ConstBitIterator */

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
    /*
    Debug.printf("boolattr",
                 "underlying word at 0x%p looks like 0x%016llx, bit is %u\n",
                 &(*i).second,
                 (unsigned long long)((*i).second),
                 unsigned(k.first));
    */
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
    /*
    Debug.printf("boolattr",
                 "underlying word at 0x%p looks like 0x%016llx, bit is %u\n",
                 &(*i).second,
                 (unsigned long long)((*i).second),
                 unsigned(k.first));
    */
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

  /**
   * Delete all flags from the given node.
   */
  void erase(NodeValue* nv) {
    super::erase(nv);
  }

  /**
   * Clear the hash table.
   */
  void clear() {
    super::clear();
  }

  /** Is the hash table empty? */
  bool empty() const {
    return super::empty();
  }

  /** This is currently very misleading! */
  size_t size() const {
    return super::size();
  }
};/* class AttrHash<bool> */

/**
 * A "CDAttrHash<value_type>"---the hash table underlying
 * attributes---is simply a context-dependent mapping of
 * pair<unique-attribute-id, Node> to value_type using our specialized
 * hash function for these pairs.
 */
template <class value_type>
class CDAttrHash :
    public context::CDHashMap<std::pair<uint64_t, NodeValue*>,
                          value_type,
                          AttrHashFunction> {
public:
  CDAttrHash(context::Context* ctxt) :
    context::CDHashMap<std::pair<uint64_t, NodeValue*>,
                   value_type,
                   AttrHashFunction>(ctxt) {
  }
};/* class CDAttrHash<> */

/**
 * In the case of Boolean-valued attributes we have a special
 * "CDAttrHash<bool>" to pack bits together in words.
 */
template <>
class CDAttrHash<bool> :
    protected context::CDHashMap<NodeValue*,
                             uint64_t,
                             AttrBoolHashFunction> {

  /** A "super" type, like in Java, for easy reference below. */
  typedef context::CDHashMap<NodeValue*, uint64_t, AttrBoolHashFunction> super;

  /**
   * BitAccessor allows us to return a bit "by reference."  Of course,
   * we don't require bit-addressibility supported by the system, we
   * do it with a complex type.
   */
  class BitAccessor {

    super& d_map;

    NodeValue* d_key;

    uint64_t d_word;

    unsigned d_bit;

  public:

    BitAccessor(super& map, NodeValue* key, uint64_t word, unsigned bit) :
      d_map(map),
      d_key(key),
      d_word(word),
      d_bit(bit) {
      /*
      Debug.printf("cdboolattr",
                   "CDAttrHash<bool>::BitAccessor(%p, %p, %016llx, %u)\n",
                   &map, key, (unsigned long long) word, bit);
      */
    }

    BitAccessor& operator=(bool b) {
      if(b) {
        // set the bit
        d_word |= (1 << d_bit);
        d_map.insert(d_key, d_word);
        /*
        Debug.printf("cdboolattr",
                     "CDAttrHash<bool>::BitAccessor::set(%p, %p, %016llx, %u)\n",
                     &d_map, d_key, (unsigned long long) d_word, d_bit);
        */
      } else {
        // clear the bit
        d_word &= ~(1 << d_bit);
        d_map.insert(d_key, d_word);
        /*
        Debug.printf("cdboolattr",
                     "CDAttrHash<bool>::BitAccessor::clr(%p, %p, %016llx, %u)\n",
                     &d_map, d_key, (unsigned long long) d_word, d_bit);
        */
      }

      return *this;
    }

    operator bool() const {
      /*
      Debug.printf("cdboolattr",
                   "CDAttrHash<bool>::BitAccessor::toBool(%p, %p, %016llx, %u)\n",
                   &d_map, d_key, (unsigned long long) d_word, d_bit);
      */
      return (d_word & (1 << d_bit)) ? true : false;
    }
  };/* class CDAttrHash<bool>::BitAccessor */

  /**
   * A (somewhat degenerate) const_iterator over boolean-valued
   * attributes.  This const_iterator doesn't support anything except
   * comparison and dereference.  It's intended just for the result of
   * find() on the table.
   */
  class ConstBitIterator {

    const std::pair<NodeValue* const, uint64_t> d_entry;

    unsigned d_bit;

  public:

    ConstBitIterator() :
      d_entry(),
      d_bit(0) {
    }

    ConstBitIterator(const std::pair<NodeValue* const, uint64_t>& entry,
                     unsigned bit) :
      d_entry(entry),
      d_bit(bit) {
    }

    std::pair<NodeValue* const, bool> operator*() {
      return std::make_pair(d_entry.first,
                            (d_entry.second & (1 << d_bit)) ? true : false);
    }

    bool operator==(const ConstBitIterator& b) {
      return d_entry == b.d_entry && d_bit == b.d_bit;
    }
  };/* class CDAttrHash<bool>::ConstBitIterator */

  /* remove non-permitted operations */
  CDAttrHash(const CDAttrHash<bool>&) CVC4_UNDEFINED;
  CDAttrHash<bool>& operator=(const CDAttrHash<bool>&) CVC4_UNDEFINED;

public:

  CDAttrHash(context::Context* context) : super(context) { }

  typedef std::pair<uint64_t, NodeValue*> key_type;
  typedef bool data_type;
  typedef std::pair<const key_type, data_type> value_type;

  /** an iterator type; see above for limitations */
  typedef ConstBitIterator iterator;
  /** a const_iterator type; see above for limitations */
  typedef ConstBitIterator const_iterator;

  /**
   * Find the boolean value in the hash table.  Returns something ==
   * end() if not found.
   */
  ConstBitIterator find(const std::pair<uint64_t, NodeValue*>& k) const {
    super::const_iterator i = super::find(k.second);
    if(i == super::end()) {
      return ConstBitIterator();
    }
    /*
    Debug.printf("cdboolattr",
                 "underlying word at address looks like 0x%016llx, bit is %u\n",
                 (unsigned long long)((*i).second),
                 unsigned(k.first));
    */
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
    uint64_t word = super::operator[](k.second);
    return BitAccessor(*this, k.second, word, k.first);
  }

  /**
   * Delete all flags from the given node.  Simply calls superclass's
   * obliterate().  Note this removes all attributes at all context
   * levels for this NodeValue!  This is important when the NodeValue
   * is no longer referenced and is being collected, but otherwise
   * it probably isn't useful to do this.
   */
  void erase(NodeValue* nv) {
    super::obliterate(nv);
  }

  /**
   * Clear the hash table.  This simply exposes the protected superclass
   * version of clear() to clients.
   */
  void clear() {
    super::clear();
  }

  /** Is the hash table empty? */
  bool empty() const {
    return super::empty();
  }

  /** This is currently very misleading! */
  size_t size() const {
    return super::size();
  }

};/* class CDAttrHash<bool> */

}/* CVC4::expr::attr namespace */

// ATTRIBUTE CLEANUP FUNCTIONS =================================================

namespace attr {

/** Default cleanup for unmanaged Attribute<> */
struct NullCleanupStrategy {
};/* struct NullCleanupStrategy */

/** Default cleanup for ManagedAttribute<> */
template <class T>
struct ManagedAttributeCleanupStrategy {
};/* struct ManagedAttributeCleanupStrategy<> */

/** Specialization for T* */
template <class T>
struct ManagedAttributeCleanupStrategy<T*> {
  static inline void cleanup(T* p) { delete p; }
};/* struct ManagedAttributeCleanupStrategy<T*> */

/** Specialization for const T* */
template <class T>
struct ManagedAttributeCleanupStrategy<const T*> {
  static inline void cleanup(const T* p) { delete p; }
};/* struct ManagedAttributeCleanupStrategy<const T*> */

/**
 * Helper for Attribute<> class below to determine whether a cleanup
 * is defined or not.
 */
template <class T, class C>
struct getCleanupStrategy {
  typedef T value_type;
  typedef KindValueToTableValueMapping<value_type> mapping;
  static void fn(typename mapping::table_value_type t) {
    C::cleanup(mapping::convertBack(t));
  }
};/* struct getCleanupStrategy<> */

/**
 * Specialization for NullCleanupStrategy.
 */
template <class T>
struct getCleanupStrategy<T, NullCleanupStrategy> {
  typedef T value_type;
  typedef KindValueToTableValueMapping<value_type> mapping;
  static void (*const fn)(typename mapping::table_value_type);
};/* struct getCleanupStrategy<T, NullCleanupStrategy> */

// out-of-class initialization required (because it's a non-integral type)
template <class T>
void (*const getCleanupStrategy<T, NullCleanupStrategy>::fn)
     (typename getCleanupStrategy<T, NullCleanupStrategy>::
               mapping::table_value_type) = NULL;

/**
 * Specialization for ManagedAttributeCleanupStrategy<T>.
 */
template <class T>
struct getCleanupStrategy<T, ManagedAttributeCleanupStrategy<T> > {
  typedef T value_type;
  typedef KindValueToTableValueMapping<value_type> mapping;
  static void (*const fn)(typename mapping::table_value_type);
};/* struct getCleanupStrategy<T, ManagedAttributeCleanupStrategy<T> > */

// out-of-class initialization required (because it's a non-integral type)
template <class T>
void (*const getCleanupStrategy<T, ManagedAttributeCleanupStrategy<T> >::fn)
     (typename getCleanupStrategy<T, ManagedAttributeCleanupStrategy<T> >::
               mapping::table_value_type) = NULL;

/**
 * Specialization for ManagedAttributeCleanupStrategy<T*>.
 */
template <class T>
struct getCleanupStrategy<T*, ManagedAttributeCleanupStrategy<T*> > {
  typedef T* value_type;
  typedef ManagedAttributeCleanupStrategy<value_type> C;
  typedef KindValueToTableValueMapping<value_type> mapping;
  static void fn(typename mapping::table_value_type t) {
    C::cleanup(mapping::convertBack(t));
  }
};/* struct getCleanupStrategy<T*, ManagedAttributeCleanupStrategy<T*> > */

/**
 * Specialization for ManagedAttributeCleanupStrategy<const T*>.
 */
template <class T>
struct getCleanupStrategy<const T*,
                          ManagedAttributeCleanupStrategy<const T*> > {
  typedef const T* value_type;
  typedef ManagedAttributeCleanupStrategy<value_type> C;
  typedef KindValueToTableValueMapping<value_type> mapping;
  static void fn(typename mapping::table_value_type t) {
    C::cleanup(mapping::convertBack(t));
  }
};/* struct getCleanupStrategy<const T*,
                               ManagedAttributeCleanupStrategy<const T*> > */

/**
 * Cause compile-time error for improperly-instantiated
 * getCleanupStrategy<>.
 */
template <class T, class U>
struct getCleanupStrategy<T, ManagedAttributeCleanupStrategy<U> >;

}/* CVC4::expr::attr namespace */

// ATTRIBUTE IDENTIFIER ASSIGNMENT TEMPLATE ====================================

namespace attr {

/**
 * This is the last-attribute-assigner.  IDs are not globally
 * unique; rather, they are unique for each table_value_type.
 */
template <class T, bool context_dep>
struct LastAttributeId {
  static uint64_t& getId() {
    static uint64_t s_id = 0;
    return s_id;
  }
};

}/* CVC4::expr::attr namespace */

// ATTRIBUTE TRAITS ============================================================

namespace attr {

/**
 * This is the last-attribute-assigner.  IDs are not globally
 * unique; rather, they are unique for each table_value_type.
 */
template <class T, bool context_dep>
struct AttributeTraits {
  typedef void (*cleanup_t)(T);
  static std::vector<cleanup_t>& getCleanup() {
    static std::vector<cleanup_t> cleanup;
    return cleanup;
  }
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
 * @param CleanupStrategy Clean-up routine for associated values when the
 * Node goes away.  Useful, e.g., for pointer-valued attributes when
 * the values are "owned" by the table.
 *
 * @param context_dep whether this attribute kind is
 * context-dependent
 */
template <class T,
          class value_t,
          class CleanupStrategy = attr::NullCleanupStrategy,
          bool context_dep = false>
class Attribute {
  /**
   * The unique ID associated to this attribute.  Assigned statically,
   * at load time.
   */
  static const uint64_t s_id;

public:

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

  /**
   * Expose this setting to the users of this Attribute kind.
   */
  static const bool context_dependent = context_dep;

  /**
   * Register this attribute kind and check that the ID is a valid ID
   * for bool-valued attributes.  Fail an assert if not.  Otherwise
   * return the id.
   */
  static inline uint64_t registerAttribute() {
    typedef typename attr::KindValueToTableValueMapping<value_t>::
                     table_value_type table_value_type;
    typedef attr::AttributeTraits<table_value_type, context_dep> traits;
    uint64_t id = attr::LastAttributeId<table_value_type, context_dep>::getId()++;
    Assert(traits::getCleanup().size() == id);// sanity check
    traits::getCleanup().push_back(attr::getCleanupStrategy<value_t,
                                                       CleanupStrategy>::fn);
    return id;
  }
};/* class Attribute<> */

/**
 * An "attribute type" structure for boolean flags (special).  The
 * full one is below; the existence of this one disallows for boolean
 * flag attributes with a specialized cleanup function.
 */
/* -- doesn't work; other specialization is "more specific" ??
template <class T, class CleanupStrategy, bool context_dep>
class Attribute<T, bool, CleanupStrategy, context_dep> {
  template <bool> struct ERROR_bool_attributes_cannot_have_cleanup_functions;
  ERROR_bool_attributes_cannot_have_cleanup_functions<true> blah;
};
*/

/**
 * An "attribute type" structure for boolean flags (special).
 */
template <class T, bool context_dep>
class Attribute<T, bool, attr::NullCleanupStrategy, context_dep> {
  /** IDs for bool-valued attributes are actually bit assignments. */
  static const uint64_t s_id;

public:

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
   * Expose this setting to the users of this Attribute kind.
   */
  static const bool context_dependent = context_dep;

  /**
   * Register this attribute kind and check that the ID is a valid ID
   * for bool-valued attributes.  Fail an assert if not.  Otherwise
   * return the id.
   */
  static inline uint64_t registerAttribute() {
    uint64_t id = attr::LastAttributeId<bool, context_dep>::getId()++;
    AlwaysAssert( id <= 63,
                  "Too many boolean node attributes registered "
                  "during initialization !" );
    return id;
  }
};/* class Attribute<..., bool, ...> */

/**
 * This is a context-dependent attribute kind (the only difference
 * between CDAttribute<> and Attribute<> (with the fourth argument
 * "true") is that you cannot supply a cleanup function (a no-op one
 * is used).
 */
template <class T,
          class value_type>
struct CDAttribute :
    public Attribute<T, value_type, attr::NullCleanupStrategy, true> {};

/**
 * This is a managed attribute kind (the only difference between
 * ManagedAttribute<> and Attribute<> is the default cleanup function
 * and the fact that ManagedAttributes cannot be context-dependent).
 * In the default ManagedAttribute cleanup function, the value is
 * destroyed with the delete operator.  If the value is allocated with
 * the array version of new[], an alternate cleanup function should be
 * provided that uses array delete[].  It is an error to create a
 * ManagedAttribute<> kind with a non-pointer value_type if you don't
 * also supply a custom cleanup function.
 */
template <class T,
          class value_type,
          class CleanupStrategy =
                    attr::ManagedAttributeCleanupStrategy<value_type> >
struct ManagedAttribute :
    public Attribute<T, value_type, CleanupStrategy, false> {};

// ATTRIBUTE IDENTIFIER ASSIGNMENT =============================================

/** Assign unique IDs to attributes at load time. */
// Use of the comma-operator here forces instantiation (and
// initialization) of the AttributeTraits<> structure and its
// "cleanup" vector before registerAttribute() is called.  This is
// important because otherwise the vector is initialized later,
// clearing the first-pushed cleanup function.
template <class T, class value_t, class CleanupStrategy, bool context_dep>
const uint64_t Attribute<T, value_t, CleanupStrategy, context_dep>::s_id =
  ( attr::AttributeTraits<typename attr::KindValueToTableValueMapping<value_t>::
                                   table_value_type,
                          context_dep>::getCleanup().size(),
    Attribute<T, value_t, CleanupStrategy, context_dep>::registerAttribute() );

/** Assign unique IDs to attributes at load time. */
template <class T, bool context_dep>
const uint64_t Attribute<T,
                         bool,
                         attr::NullCleanupStrategy, context_dep>::s_id =
  Attribute<T, bool, attr::NullCleanupStrategy, context_dep>::
    registerAttribute();

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* __CVC4__EXPR__ATTRIBUTE_INTERNALS_H */
