/*********************                                                        */
/*! \file attribute_internals.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Node attributes' internals.
 **
 ** Node attributes' internals.
 **/

#include "cvc4_private.h"

#ifndef CVC4_ATTRIBUTE_H__INCLUDING__ATTRIBUTE_INTERNALS_H
#  error expr/attribute_internals.h should only be included by expr/attribute.h
#endif /* CVC4_ATTRIBUTE_H__INCLUDING__ATTRIBUTE_INTERNALS_H */

#ifndef CVC4__EXPR__ATTRIBUTE_INTERNALS_H
#define CVC4__EXPR__ATTRIBUTE_INTERNALS_H

#include <cstdint>
#include <unordered_map>

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
 *
 * The `Enable` template parameter is used to instantiate the template
 * conditionally: If the template substitution of Enable fails (e.g. when using
 * `std::enable_if` in the template parameter and the condition is false), the
 * instantiation is ignored due to the SFINAE rule.
 */
template <class T, class Enable = void>
struct KindValueToTableValueMapping
{
  /** Simple case: T == table_value_type */
  typedef T table_value_type;
  /** No conversion necessary */
  inline static T convert(const T& t) { return t; }
  /** No conversion necessary */
  inline static T convertBack(const T& t) { return t; }
};

/**
 * This converts arbitrary unsigned integers (up to 64-bit) to and from 64-bit
 * integers s.t. they can be stored in the hash table for integral-valued
 * attributes.
 */
template <class T>
struct KindValueToTableValueMapping<
    T,
    // Use this specialization only for unsigned integers
    typename std::enable_if<std::is_unsigned<T>::value>::type>
{
  typedef uint64_t table_value_type;
  /** Convert from unsigned integer to uint64_t */
  static uint64_t convert(const T& t)
  {
    static_assert(sizeof(T) <= sizeof(uint64_t),
                  "Cannot store integer attributes of a bit-width that is "
                  "greater than 64-bits");
    return static_cast<uint64_t>(t);
  }
  /** Convert from uint64_t to unsigned integer */
  static T convertBack(const uint64_t& t) { return static_cast<T>(t); }
};

}/* CVC4::expr::attr namespace */

// ATTRIBUTE HASH TABLES =======================================================

namespace attr {

// Returns a 64 bit integer with a single `bit` set when `bit` < 64.
// Avoids problems in (1 << x) when sizeof(x) <= sizeof(uint64_t).
inline uint64_t GetBitSet(uint64_t bit)
{
  constexpr uint64_t kOne = 1;
  return kOne << bit;
}

/**
 * An "AttrHash<value_type>"---the hash table underlying
 * attributes---is simply a mapping of pair<unique-attribute-id, Node>
 * to value_type using our specialized hash function for these pairs.
 */
template <class value_type>
class AttrHash :
    public std::unordered_map<std::pair<uint64_t, NodeValue*>,
                               value_type,
                               AttrHashFunction> {
};/* class AttrHash<> */

/**
 * In the case of Boolean-valued attributes we have a special
 * "AttrHash<bool>" to pack bits together in words.
 */
template <>
class AttrHash<bool> :
    protected std::unordered_map<NodeValue*,
                                  uint64_t,
                                  AttrBoolHashFunction> {

  /** A "super" type, like in Java, for easy reference below. */
  typedef std::unordered_map<NodeValue*, uint64_t, AttrBoolHashFunction> super;

  /**
   * BitAccessor allows us to return a bit "by reference."  Of course,
   * we don't require bit-addressibility supported by the system, we
   * do it with a complex type.
   */
  class BitAccessor {

    uint64_t& d_word;

    uint64_t d_bit;

   public:
    BitAccessor(uint64_t& word, uint64_t bit) : d_word(word), d_bit(bit) {}

    BitAccessor& operator=(bool b) {
      if(b) {
        // set the bit
        d_word |= GetBitSet(d_bit);
      } else {
        // clear the bit
        d_word &= ~GetBitSet(d_bit);
      }

      return *this;
    }

    operator bool() const { return (d_word & GetBitSet(d_bit)) ? true : false; }
  };/* class AttrHash<bool>::BitAccessor */

  /**
   * A (somewhat degenerate) iterator over boolean-valued attributes.
   * This iterator doesn't support anything except comparison and
   * dereference.  It's intended just for the result of find() on the
   * table.
   */
  class BitIterator {

    std::pair<NodeValue* const, uint64_t>* d_entry;

    uint64_t d_bit;

   public:

    BitIterator() :
      d_entry(NULL),
      d_bit(0) {
    }

    BitIterator(std::pair<NodeValue* const, uint64_t>& entry, uint64_t bit)
        : d_entry(&entry), d_bit(bit)
    {
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

    uint64_t d_bit;

   public:

    ConstBitIterator() :
      d_entry(NULL),
      d_bit(0) {
    }

    ConstBitIterator(const std::pair<NodeValue* const, uint64_t>& entry,
                     uint64_t bit)
        : d_entry(&entry), d_bit(bit)
    {
    }

    std::pair<NodeValue* const, bool> operator*()
    {
      return std::make_pair(
          d_entry->first, (d_entry->second & GetBitSet(d_bit)) ? true : false);
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
                 (uint64_t)((*i).second),
                 uint64_t(k.first));
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
                 (uint64_t)((*i).second),
                 uint64_t(k.first));
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

}/* CVC4::expr::attr namespace */

// ATTRIBUTE IDENTIFIER ASSIGNMENT TEMPLATE ====================================

namespace attr {

/**
 * This is the last-attribute-assigner.  IDs are not globally
 * unique; rather, they are unique for each table_value_type.
 */
template <class T, bool context_dep>
struct LastAttributeId {
 public:
  static uint64_t getNextId() {
    uint64_t* id = raw_id();
    const uint64_t next_id = *id;
    ++(*id);
    return next_id;
  }
  static uint64_t getId() {
    return *raw_id();
  }
 private:
  static uint64_t* raw_id()
  {
    static uint64_t s_id = 0;
    return &s_id;
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
 * @param context_dep whether this attribute kind is
 * context-dependent
 */
template <class T, class value_t, bool context_dep = false>
class Attribute
{
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
    return attr::LastAttributeId<table_value_type, context_dep>::getNextId();
  }
};/* class Attribute<> */

/**
 * An "attribute type" structure for boolean flags (special).
 */
template <class T, bool context_dep>
class Attribute<T, bool, context_dep>
{
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
    const uint64_t id = attr::LastAttributeId<bool, context_dep>::getNextId();
    AlwaysAssert(id <= 63) << "Too many boolean node attributes registered "
                              "during initialization !";
    return id;
  }
};/* class Attribute<..., bool, ...> */

// ATTRIBUTE IDENTIFIER ASSIGNMENT =============================================

/** Assign unique IDs to attributes at load time. */
template <class T, class value_t, bool context_dep>
const uint64_t Attribute<T, value_t, context_dep>::s_id =
    Attribute<T, value_t,  context_dep>::registerAttribute();


/** Assign unique IDs to attributes at load time. */
template <class T, bool context_dep>
const uint64_t Attribute<T, bool, context_dep>::s_id =
    Attribute<T, bool, context_dep>::registerAttribute();

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* CVC4__EXPR__ATTRIBUTE_INTERNALS_H */
