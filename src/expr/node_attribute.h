/*********************                                           -*- C++ -*-  */
/** node_attribute.h
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
 **/

#ifndef __CVC4__EXPR__NODE_ATTRIBUTE_H
#define __CVC4__EXPR__NODE_ATTRIBUTE_H

#include <stdint.h>
#include "config.h"
#include "context/context.h"
#include "expr/node.h"

namespace CVC4 {
namespace expr {

template <class value_type>
class AttrTables;

// global (or TSS)
extern CDMap<uint64_t> g_hash_bool;
extern CDMap<uint64_t> g_hash_int;
extern CDMap<Node>     g_hash_expr;
extern CDMap<void*>    g_hash_ptr;

template <class T>
class AttrTable;

template <>
class AttrTable<bool> {
public:
  class BitAccessor {
    uint64_t& d_word;
    unsigned d_bit;
  public:
    BitAccessor& operator=(bool b);
    // continue...
  };

  // bool specialization
  static CDMap<uint64_t> *s_hash;

  template <class Attr>
  BitAccessor& find(Node e, const Attr&);

  template <class Attr>
  bool find(Node e, const Attr&) const;
};

template <>
class AttrTable<uint64_t> {
public:  
  // int(egral) specialization
  static CDMap<uint64_t> *s_hash;
  uint64_t& find(Node);
  uint64_t& find(Node) const;
};

template <class T>
class AttrTable<T*> {
  // pointer specialization
  static CDMap<void*> *s_hash;
public:
};

template <>
class AttrTable<Node> {
public:
  // Node specialization
  static CDMap<Node> *s_hash;
  Node find(Node);
};

CDMap<uint64_t>* AttrTable<bool>::s_hash     = &g_hash_bool;
CDMap<uint64_t>* AttrTable<uint64_t>::s_hash = &g_hash_int;
CDMap<Node>*     AttrTable<Node>::s_hash     = &g_hash_expr;

template <class T>
CDMap<void*>*    AttrTable<T*>::s_hash       = &g_hash_ptr;

template <class Attr>
class AttributeTable {
  typedef typename Attr::value_type value_type;

  AttrTable<value_type>& d_table;
  
};

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* __CVC4__EXPR__EXPR_ATTRIBUTE_H */
