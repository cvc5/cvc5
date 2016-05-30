/*********************                                                        */
/*! \file attribute.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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
#include "context/context.h"

#ifndef __CVC4__EXPR__ATTRIBUTE_H
#define __CVC4__EXPR__ATTRIBUTE_H

#include <string>
#include <stdint.h>
#include "expr/attribute_unique_id.h"

// include supporting templates
#define CVC4_ATTRIBUTE_H__INCLUDING__ATTRIBUTE_INTERNALS_H
#include "expr/attribute_internals.h"
#undef CVC4_ATTRIBUTE_H__INCLUDING__ATTRIBUTE_INTERNALS_H

namespace CVC4 {

class SmtEngine;

namespace smt {
  extern CVC4_THREADLOCAL(SmtEngine*) s_smtEngine_current;
}/* CVC4::smt namespace */

namespace expr {
namespace attr {

// ATTRIBUTE MANAGER ===========================================================

struct SmtAttributes {
  SmtAttributes(context::Context*);

  // IF YOU ADD ANY TABLES, don't forget to add them also to the
  // implementation of deleteAllAttributes().

  /** Underlying hash table for context-dependent boolean-valued attributes */
  CDAttrHash<bool> d_cdbools;
  /** Underlying hash table for context-dependent integral-valued attributes */
  CDAttrHash<uint64_t> d_cdints;
  /** Underlying hash table for context-dependent node-valued attributes */
  CDAttrHash<TNode> d_cdtnodes;
  /** Underlying hash table for context-dependent node-valued attributes */
  CDAttrHash<Node> d_cdnodes;
  /** Underlying hash table for context-dependent string-valued attributes */
  CDAttrHash<std::string> d_cdstrings;
  /** Underlying hash table for context-dependent pointer-valued attributes */
  CDAttrHash<void*> d_cdptrs;

  /** Delete all attributes of given node */
  void deleteAllAttributes(TNode n);

  template <class T>
  void deleteFromTable(CDAttrHash<T>& table, NodeValue* nv);

};/* struct SmtAttributes */

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
  template <class T, bool context_dep>
  friend struct getTable;

  bool d_inGarbageCollection;

  void clearDeleteAllAttributesBuffer();

  SmtAttributes& getSmtAttributes(SmtEngine*);
  const SmtAttributes& getSmtAttributes(SmtEngine*) const;

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
  /** Underlying hash table for pointer-valued attributes */
  AttrHash<void*> d_ptrs;

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
 */
template <class T, bool context_dep>
struct getTable;

/** Access the "d_bools" member of AttributeManager. */
template <>
struct getTable<bool, false> {
  static const AttrTableId id = AttrTableBool;
  typedef AttrHash<bool> table_type;
  static inline table_type& get(AttributeManager& am, SmtEngine* smt) {
    return am.d_bools;
  }
  static inline const table_type& get(const AttributeManager& am, SmtEngine* smt) {
    return am.d_bools;
  }
};

/** Access the "d_ints" member of AttributeManager. */
template <>
struct getTable<uint64_t, false> {
  static const AttrTableId id = AttrTableUInt64;
  typedef AttrHash<uint64_t> table_type;
  static inline table_type& get(AttributeManager& am, SmtEngine* smt) {
    return am.d_ints;
  }
  static inline const table_type& get(const AttributeManager& am, SmtEngine* smt) {
    return am.d_ints;
  }
};

/** Access the "d_tnodes" member of AttributeManager. */
template <>
struct getTable<TNode, false> {
  static const AttrTableId id = AttrTableTNode;
  typedef AttrHash<TNode> table_type;
  static inline table_type& get(AttributeManager& am, SmtEngine* smt) {
    return am.d_tnodes;
  }
  static inline const table_type& get(const AttributeManager& am, SmtEngine* smt) {
    return am.d_tnodes;
  }
};

/** Access the "d_nodes" member of AttributeManager. */
template <>
struct getTable<Node, false> {
  static const AttrTableId id = AttrTableNode;
  typedef AttrHash<Node> table_type;
  static inline table_type& get(AttributeManager& am, SmtEngine* smt) {
    return am.d_nodes;
  }
  static inline const table_type& get(const AttributeManager& am, SmtEngine* smt) {
    return am.d_nodes;
  }
};

/** Access the "d_types" member of AttributeManager. */
template <>
struct getTable<TypeNode, false> {
  static const AttrTableId id = AttrTableTypeNode;
  typedef AttrHash<TypeNode> table_type;
  static inline table_type& get(AttributeManager& am, SmtEngine* smt) {
    return am.d_types;
  }
  static inline const table_type& get(const AttributeManager& am, SmtEngine* smt) {
    return am.d_types;
  }
};

/** Access the "d_strings" member of AttributeManager. */
template <>
struct getTable<std::string, false> {
  static const AttrTableId id = AttrTableString;
  typedef AttrHash<std::string> table_type;
  static inline table_type& get(AttributeManager& am, SmtEngine* smt) {
    return am.d_strings;
  }
  static inline const table_type& get(const AttributeManager& am, SmtEngine* smt) {
    return am.d_strings;
  }
};

/** Access the "d_ptrs" member of AttributeManager. */
template <class T>
struct getTable<T*, false> {
  static const AttrTableId id = AttrTablePointer;
  typedef AttrHash<void*> table_type;
  static inline table_type& get(AttributeManager& am, SmtEngine* smt) {
    return am.d_ptrs;
  }
  static inline const table_type& get(const AttributeManager& am, SmtEngine* smt) {
    return am.d_ptrs;
  }
};

/** Access the "d_ptrs" member of AttributeManager. */
template <class T>
struct getTable<const T*, false> {
  static const AttrTableId id = AttrTablePointer;
  typedef AttrHash<void*> table_type;
  static inline table_type& get(AttributeManager& am, SmtEngine* smt) {
    return am.d_ptrs;
  }
  static inline const table_type& get(const AttributeManager& am, SmtEngine* smt) {
    return am.d_ptrs;
  }
};

/** Access the "d_cdbools" member of AttributeManager. */
template <>
struct getTable<bool, true> {
  static const AttrTableId id = AttrTableCDBool;
  typedef CDAttrHash<bool> table_type;
  static inline table_type& get(AttributeManager& am, SmtEngine* smt) {
    return am.getSmtAttributes(smt).d_cdbools;
  }
  static inline const table_type& get(const AttributeManager& am, SmtEngine* smt) {
    return am.getSmtAttributes(smt).d_cdbools;
  }
};

/** Access the "d_cdints" member of AttributeManager. */
template <>
struct getTable<uint64_t, true> {
  static const AttrTableId id = AttrTableCDUInt64;
  typedef CDAttrHash<uint64_t> table_type;
  static inline table_type& get(AttributeManager& am, SmtEngine* smt) {
    return am.getSmtAttributes(smt).d_cdints;
  }
  static inline const table_type& get(const AttributeManager& am, SmtEngine* smt) {
    return am.getSmtAttributes(smt).d_cdints;
  }
};

/** Access the "d_tnodes" member of AttributeManager. */
template <>
struct getTable<TNode, true> {
  static const AttrTableId id = AttrTableCDTNode;
  typedef CDAttrHash<TNode> table_type;
  static inline table_type& get(AttributeManager& am, SmtEngine* smt) {
    return am.getSmtAttributes(smt).d_cdtnodes;
  }
  static inline const table_type& get(const AttributeManager& am, SmtEngine* smt) {
    return am.getSmtAttributes(smt).d_cdtnodes;
  }
};

/** Access the "d_cdnodes" member of AttributeManager. */
template <>
struct getTable<Node, true> {
  static const AttrTableId id = AttrTableCDNode;
  typedef CDAttrHash<Node> table_type;
  static inline table_type& get(AttributeManager& am, SmtEngine* smt) {
    return am.getSmtAttributes(smt).d_cdnodes;
  }
  static inline const table_type& get(const AttributeManager& am, SmtEngine* smt) {
    return am.getSmtAttributes(smt).d_cdnodes;
  }
};

/** Access the "d_cdstrings" member of AttributeManager. */
template <>
struct getTable<std::string, true> {
  static const AttrTableId id = AttrTableCDString;
  typedef CDAttrHash<std::string> table_type;
  static inline table_type& get(AttributeManager& am, SmtEngine* smt) {
    return am.getSmtAttributes(smt).d_cdstrings;
  }
  static inline const table_type& get(const AttributeManager& am, SmtEngine* smt) {
    return am.getSmtAttributes(smt).d_cdstrings;
  }
};

/** Access the "d_cdptrs" member of AttributeManager. */
template <class T>
struct getTable<T*, true> {
  static const AttrTableId id = AttrTableCDPointer;
  typedef CDAttrHash<void*> table_type;
  static inline table_type& get(AttributeManager& am, SmtEngine* smt) {
    return am.getSmtAttributes(smt).d_cdptrs;
  }
  static inline const table_type& get(const AttributeManager& am, SmtEngine* smt) {
    return am.getSmtAttributes(smt).d_cdptrs;
  }
};

/** Access the "d_cdptrs" member of AttributeManager. */
template <class T>
struct getTable<const T*, true> {
  static const AttrTableId id = AttrTableCDPointer;
  typedef CDAttrHash<void*> table_type;
  static inline table_type& get(AttributeManager& am, SmtEngine* smt) {
    return am.getSmtAttributes(smt).d_cdptrs;
  }
  static inline const table_type& get(const AttributeManager& am, SmtEngine* smt) {
    return am.getSmtAttributes(smt).d_cdptrs;
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
    getTable<value_type, AttrKind::context_dependent>::get(*this, smt::s_smtEngine_current);
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
      getTable<value_type, AttrKind::context_dependent>::get(*am, smt::s_smtEngine_current);
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
      getTable<value_type, AttrKind::context_dependent>::get(*am, smt::s_smtEngine_current);
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
      getTable<value_type, AttrKind::context_dependent>::get(*am, smt::s_smtEngine_current);
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
    getTable<value_type, AttrKind::context_dependent>::get(*this, smt::s_smtEngine_current);
  ah[std::make_pair(AttrKind::getId(), nv)] = mapping::convert(value);
}

/**
 * Search for the NodeValue in all attribute tables and remove it,
 * calling the cleanup function if one is defined.
 *
 * This cannot use nv as anything other than a pointer!
 */
template <class T>
inline void AttributeManager::deleteFromTable(AttrHash<T>& table,
                                              NodeValue* nv) {
  for(uint64_t id = 0; id < attr::LastAttributeId<T, false>::getId(); ++id) {
    typedef AttributeTraits<T, false> traits_t;
    typedef AttrHash<T> hash_t;
    std::pair<uint64_t, NodeValue*> pr = std::make_pair(id, nv);
    if(traits_t::getCleanup()[id] != NULL) {
      typename hash_t::iterator i = table.find(pr);
      if(i != table.end()) {
        traits_t::getCleanup()[id]((*i).second);
        table.erase(pr);
      }
    } else {
      table.erase(pr);
    }
  }
}

/**
 * Obliterate a NodeValue from a (context-dependent) attribute table.
 */
template <class T>
inline void SmtAttributes::deleteFromTable(CDAttrHash<T>& table,
                                           NodeValue* nv) {
  for(unsigned id = 0; id < attr::LastAttributeId<T, true>::getId(); ++id) {
    table.obliterate(std::make_pair(id, nv));
  }
}

/**
 * Remove all attributes from the table calling the cleanup function
 * if one is defined.
 */
template <class T>
inline void AttributeManager::deleteAllFromTable(AttrHash<T>& table) {
  Assert(!d_inGarbageCollection);
  d_inGarbageCollection = true;

  bool anyRequireClearing = false;
  typedef AttributeTraits<T, false> traits_t;
  typedef AttrHash<T> hash_t;
  for(uint64_t id = 0; id < attr::LastAttributeId<T, false>::getId(); ++id) {
    if(traits_t::getCleanup()[id] != NULL) {
      anyRequireClearing = true;
    }
  }

  if(anyRequireClearing) {
    typename hash_t::iterator it = table.begin();
    typename hash_t::iterator it_end = table.end();

    while (it != it_end){
      uint64_t id = (*it).first.first;
      /*
      Debug("attrgc") << "id " << id
                      << " node_value: " << ((*it).first.second)
                      << std::endl;
      */
      if(traits_t::getCleanup()[id] != NULL) {
        traits_t::getCleanup()[id]((*it).second);
      }
      ++it;
    }
  }
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
  typedef AttributeTraits<T, false> traits_t;
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
      if(traits_t::getCleanup()[id] != NULL) {
        traits_t::getCleanup()[id]((*tmp).second);
      }
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

#endif /* __CVC4__EXPR__ATTRIBUTE_H */
