/*********************                                                        */
/*! \file attribute.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Node attributes.
 **
 ** Node attributes.
 **/

#include "cvc4_private.h"

/* There are strong constraints on ordering of declarations of
 * attributes and nodes due to template use */
#include "expr/node.h"
#include "expr/type_node.h"

#ifndef CVC4__EXPR__ATTRIBUTE_H
#define CVC4__EXPR__ATTRIBUTE_H

#include <string>
#include <stdint.h>
#include "expr/attribute_unique_id.h"

// include supporting templates
#define CVC4_ATTRIBUTE_H__INCLUDING__ATTRIBUTE_INTERNALS_H
#include "expr/attribute_internals.h"
#undef CVC4_ATTRIBUTE_H__INCLUDING__ATTRIBUTE_INTERNALS_H

namespace CVC4 {
namespace expr {
namespace attr {

// ATTRIBUTE MANAGER ===========================================================

/**
 * A container for the main attribute tables of the system.  There's a
 * one-to-one NodeManager : AttributeManager correspondence.
 */
class AttributeManager {

  template <class T>
  void deleteFromTable(AttrHash<T>& table, NodeValue* nv);

  template <class T>
  void deleteAllFromTable(AttrHash<T>& table);

  template <class T>
  void deleteAttributesFromTable(AttrHash<T>& table, const std::vector<uint64_t>& ids);

  template <class T>
  void reconstructTable(AttrHash<T>& table);

  /**
   * getTable<> is a helper template that gets the right table from an
   * AttributeManager given its type.
   */
  template <class T, bool context_dep, class Enable>
  friend struct getTable;

  bool d_inGarbageCollection;

  void clearDeleteAllAttributesBuffer();

public:

  /** Construct an attribute manager. */
  AttributeManager();

  // IF YOU ADD ANY TABLES, don't forget to add them also to the
  // implementation of deleteAllAttributes().

  /** Underlying hash table for boolean-valued attributes */
  AttrHash<bool> d_bools;
  /** Underlying hash table for integral-valued attributes */
  AttrHash<uint64_t> d_ints;
  /** Underlying hash table for node-valued attributes */
  AttrHash<TNode> d_tnodes;
  /** Underlying hash table for node-valued attributes */
  AttrHash<Node> d_nodes;
  /** Underlying hash table for types attributes */
  AttrHash<TypeNode> d_types;
  /** Underlying hash table for string-valued attributes */
  AttrHash<std::string> d_strings;

  /**
   * Get a particular attribute on a particular node.
   *
   * @param nv the node about which to inquire
   * @param attr the attribute kind to get
   * @return the attribute value, if set, or a default-constructed
   * AttrKind::value_type if not.
   */
  template <class AttrKind>
  typename AttrKind::value_type getAttribute(NodeValue* nv,
                                             const AttrKind& attr) const;

  /**
   * Determine if a particular attribute exists for a particular node.
   *
   * @param nv the node about which to inquire
   * @param attr the attribute kind to inquire about
   * @return true if the given node has the given attribute
   */
  template <class AttrKind>
  bool hasAttribute(NodeValue* nv,
                    const AttrKind& attr) const;

  /**
   * Determine if a particular attribute exists for a particular node,
   * and get it if it does.
   *
   * @param nv the node about which to inquire
   * @param attr the attribute kind to inquire about
   * @param ret a pointer to a return value, set in case the node has
   * the attribute
   * @return true if the given node has the given attribute
   */
  template <class AttrKind>
  bool getAttribute(NodeValue* nv,
                    const AttrKind& attr,
                    typename AttrKind::value_type& ret) const;

  /**
   * Set a particular attribute on a particular node.
   *
   * @param nv the node for which to set the attribute
   * @param attr the attribute kind to set
   * @param value a pointer to a return value, set in case the node has
   * the attribute
   * @return true if the given node has the given attribute
   */
  template <class AttrKind>
  void setAttribute(NodeValue* nv,
                    const AttrKind& attr,
                    const typename AttrKind::value_type& value);

  /**
   * Remove all attributes associated to the given node.
   *
   * @param nv the node from which to delete attributes
   */
  void deleteAllAttributes(NodeValue* nv);

  /**
   * Remove all attributes from the tables.
   */
  void deleteAllAttributes();

  /**
   * Returns true if a table is currently being deleted.
   */
  bool inGarbageCollection() const ;

  /**
   * Determines the AttrTableId of an attribute.
   *
   * @param attr the attribute
   * @return the id of the attribute table.
   */
  template <class AttrKind>
  static AttributeUniqueId getAttributeId(const AttrKind& attr);

  /** A list of attributes. */
  typedef std::vector< const AttributeUniqueId* > AttrIdVec;

  /** Deletes a list of attributes. */
  void deleteAttributes(const AttrIdVec& attributeIds);

  /**
   * debugHook() is an empty function for the purpose of debugging
   * the AttributeManager without recompiling all of CVC4.
   * Formally this is a nop.
   */
  void debugHook(int debugFlag);
};

}/* CVC4::expr::attr namespace */

// MAPPING OF ATTRIBUTE KINDS TO TABLES IN THE ATTRIBUTE MANAGER ===============

namespace attr {

/**
 * The getTable<> template provides (static) access to the
 * AttributeManager field holding the table.
 *
 * The `Enable` template parameter is used to instantiate the template
 * conditionally: If the template substitution of Enable fails (e.g. when using
 * `std::enable_if` in the template parameter and the condition is false), the
 * instantiation is ignored due to the SFINAE rule.
 */
template <class T, bool context_dep, class Enable = void>
struct getTable;

/** Access the "d_bools" member of AttributeManager. */
template <>
struct getTable<bool, false> {
  static const AttrTableId id = AttrTableBool;
  typedef AttrHash<bool> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_bools;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_bools;
  }
};

/** Access the "d_ints" member of AttributeManager. */
template <class T>
struct getTable<T,
                false,
                // Use this specialization only for unsigned integers
                typename std::enable_if<std::is_unsigned<T>::value>::type>
{
  static const AttrTableId id = AttrTableUInt64;
  typedef AttrHash<uint64_t> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_ints;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_ints;
  }
};

/** Access the "d_tnodes" member of AttributeManager. */
template <>
struct getTable<TNode, false> {
  static const AttrTableId id = AttrTableTNode;
  typedef AttrHash<TNode> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_tnodes;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_tnodes;
  }
};

/** Access the "d_nodes" member of AttributeManager. */
template <>
struct getTable<Node, false> {
  static const AttrTableId id = AttrTableNode;
  typedef AttrHash<Node> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_nodes;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_nodes;
  }
};

/** Access the "d_types" member of AttributeManager. */
template <>
struct getTable<TypeNode, false> {
  static const AttrTableId id = AttrTableTypeNode;
  typedef AttrHash<TypeNode> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_types;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_types;
  }
};

/** Access the "d_strings" member of AttributeManager. */
template <>
struct getTable<std::string, false> {
  static const AttrTableId id = AttrTableString;
  typedef AttrHash<std::string> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_strings;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_strings;
  }
};

}/* CVC4::expr::attr namespace */

// ATTRIBUTE MANAGER IMPLEMENTATIONS ===========================================

namespace attr {

// implementation for AttributeManager::getAttribute()
template <class AttrKind>
typename AttrKind::value_type
AttributeManager::getAttribute(NodeValue* nv, const AttrKind&) const {
  typedef typename AttrKind::value_type value_type;
  typedef KindValueToTableValueMapping<value_type> mapping;
  typedef typename getTable<value_type, AttrKind::context_dependent>::
            table_type table_type;

  const table_type& ah =
    getTable<value_type, AttrKind::context_dependent>::get(*this);
  typename table_type::const_iterator i =
    ah.find(std::make_pair(AttrKind::getId(), nv));

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
  static inline bool getAttribute(const AttributeManager* am,
                                  NodeValue* nv,
                                  typename AttrKind::value_type& ret) {
    typedef typename AttrKind::value_type value_type;
    typedef KindValueToTableValueMapping<value_type> mapping;
    typedef typename getTable<value_type,
                              AttrKind::context_dependent>::table_type
      table_type;

    const table_type& ah =
      getTable<value_type, AttrKind::context_dependent>::get(*am);
    typename table_type::const_iterator i =
      ah.find(std::make_pair(AttrKind::getId(), nv));

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
    //typedef KindValueToTableValueMapping<value_type> mapping;
    typedef typename getTable<value_type, AttrKind::context_dependent>::
              table_type table_type;

    const table_type& ah =
      getTable<value_type, AttrKind::context_dependent>::get(*am);
    typename table_type::const_iterator i =
      ah.find(std::make_pair(AttrKind::getId(), nv));

    if(i == ah.end()) {
      return false;
    }

    return true;
  }

  static inline bool getAttribute(const AttributeManager* am,
                                  NodeValue* nv,
                                  typename AttrKind::value_type& ret) {
    typedef typename AttrKind::value_type value_type;
    typedef KindValueToTableValueMapping<value_type> mapping;
    typedef typename getTable<value_type, AttrKind::context_dependent>::
              table_type table_type;

    const table_type& ah =
      getTable<value_type, AttrKind::context_dependent>::get(*am);
    typename table_type::const_iterator i =
      ah.find(std::make_pair(AttrKind::getId(), nv));

    if(i == ah.end()) {
      return false;
    }

    ret = mapping::convertBack((*i).second);

    return true;
  }
};

template <class AttrKind>
bool AttributeManager::hasAttribute(NodeValue* nv,
                                    const AttrKind&) const {
  return HasAttribute<AttrKind::has_default_value, AttrKind>::
           hasAttribute(this, nv);
}

template <class AttrKind>
bool AttributeManager::getAttribute(NodeValue* nv,
                                    const AttrKind&,
                                    typename AttrKind::value_type& ret) const {
  return HasAttribute<AttrKind::has_default_value, AttrKind>::
           getAttribute(this, nv, ret);
}

template <class AttrKind>
inline void
AttributeManager::setAttribute(NodeValue* nv,
                               const AttrKind&,
                               const typename AttrKind::value_type& value) {
  typedef typename AttrKind::value_type value_type;
  typedef KindValueToTableValueMapping<value_type> mapping;
  typedef typename getTable<value_type, AttrKind::context_dependent>::
            table_type table_type;

  table_type& ah =
      getTable<value_type, AttrKind::context_dependent>::get(*this);
  ah[std::make_pair(AttrKind::getId(), nv)] = mapping::convert(value);
}

/** Search for the NodeValue in all attribute tables and remove it. */
template <class T>
inline void AttributeManager::deleteFromTable(AttrHash<T>& table,
                                              NodeValue* nv) {
  // This cannot use nv as anything other than a pointer!
  const uint64_t last = attr::LastAttributeId<T, false>::getId();
  for (uint64_t id = 0; id < last; ++id)
  {
    table.erase(std::make_pair(id, nv));
  }
}

/** Remove all attributes from the table. */
template <class T>
inline void AttributeManager::deleteAllFromTable(AttrHash<T>& table) {
  Assert(!d_inGarbageCollection);
  d_inGarbageCollection = true;
  table.clear();
  d_inGarbageCollection = false;
  Assert(!d_inGarbageCollection);
}

template <class AttrKind>
AttributeUniqueId AttributeManager::getAttributeId(const AttrKind& attr){
  typedef typename AttrKind::value_type value_type;
  AttrTableId tableId = getTable<value_type,
                                 AttrKind::context_dependent>::id;
  return AttributeUniqueId(tableId, attr.getId());
}

template <class T>
void AttributeManager::deleteAttributesFromTable(AttrHash<T>& table, const std::vector<uint64_t>& ids){
  d_inGarbageCollection = true;
  typedef AttrHash<T> hash_t;

  typename hash_t::iterator it = table.begin();
  typename hash_t::iterator tmp;
  typename hash_t::iterator it_end = table.end();

  std::vector<uint64_t>::const_iterator begin_ids = ids.begin();
  std::vector<uint64_t>::const_iterator end_ids = ids.end();

  size_t initialSize = table.size();
  while (it != it_end){
    uint64_t id = (*it).first.first;

    if(std::binary_search(begin_ids, end_ids, id)){
      tmp = it;
      ++it;
      table.erase(tmp);
    }else{
      ++it;
    }
  }
  d_inGarbageCollection = false;
  static const size_t ReconstructShrinkRatio = 8;
  if(initialSize/ReconstructShrinkRatio > table.size()){
    reconstructTable(table);
  }
}

template <class T>
void AttributeManager::reconstructTable(AttrHash<T>& table){
  d_inGarbageCollection = true;
  typedef AttrHash<T> hash_t;
  hash_t cpy;
  cpy.insert(table.begin(), table.end());
  cpy.swap(table);
  d_inGarbageCollection = false;
}


}/* CVC4::expr::attr namespace */
}/* CVC4::expr namespace */

template <class AttrKind>
inline typename AttrKind::value_type
NodeManager::getAttribute(expr::NodeValue* nv, const AttrKind&) const {
  return d_attrManager->getAttribute(nv, AttrKind());
}

template <class AttrKind>
inline bool NodeManager::hasAttribute(expr::NodeValue* nv,
                                      const AttrKind&) const {
  return d_attrManager->hasAttribute(nv, AttrKind());
}

template <class AttrKind>
inline bool
NodeManager::getAttribute(expr::NodeValue* nv, const AttrKind&,
                          typename AttrKind::value_type& ret) const {
  return d_attrManager->getAttribute(nv, AttrKind(), ret);
}

template <class AttrKind>
inline void
NodeManager::setAttribute(expr::NodeValue* nv, const AttrKind&,
                          const typename AttrKind::value_type& value) {
  d_attrManager->setAttribute(nv, AttrKind(), value);
}

template <class AttrKind>
inline typename AttrKind::value_type
NodeManager::getAttribute(TNode n, const AttrKind&) const {
  return d_attrManager->getAttribute(n.d_nv, AttrKind());
}

template <class AttrKind>
inline bool
NodeManager::hasAttribute(TNode n, const AttrKind&) const {
  return d_attrManager->hasAttribute(n.d_nv, AttrKind());
}

template <class AttrKind>
inline bool
NodeManager::getAttribute(TNode n, const AttrKind&,
                          typename AttrKind::value_type& ret) const {
  return d_attrManager->getAttribute(n.d_nv, AttrKind(), ret);
}

template <class AttrKind>
inline void
NodeManager::setAttribute(TNode n, const AttrKind&,
                          const typename AttrKind::value_type& value) {
  d_attrManager->setAttribute(n.d_nv, AttrKind(), value);
}

template <class AttrKind>
inline typename AttrKind::value_type
NodeManager::getAttribute(TypeNode n, const AttrKind&) const {
  return d_attrManager->getAttribute(n.d_nv, AttrKind());
}

template <class AttrKind>
inline bool
NodeManager::hasAttribute(TypeNode n, const AttrKind&) const {
  return d_attrManager->hasAttribute(n.d_nv, AttrKind());
}

template <class AttrKind>
inline bool
NodeManager::getAttribute(TypeNode n, const AttrKind&,
                          typename AttrKind::value_type& ret) const {
  return d_attrManager->getAttribute(n.d_nv, AttrKind(), ret);
}

template <class AttrKind>
inline void
NodeManager::setAttribute(TypeNode n, const AttrKind&,
                          const typename AttrKind::value_type& value) {
  d_attrManager->setAttribute(n.d_nv, AttrKind(), value);
}

}/* CVC4 namespace */

#endif /* CVC4__EXPR__ATTRIBUTE_H */
