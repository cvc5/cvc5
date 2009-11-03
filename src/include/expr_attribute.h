/*********************                                           -*- C++ -*-  */
/** expr_attribute.h
 ** This file is part of the CVC4 prototype.
 **
 ** The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 **/

#ifndef __CVC4_EXPR_ATTRIBUTE_H
#define __CVC4_EXPR_ATTRIBUTE_H

namespace CVC4 {

template <class value_type>
class AttrTables;

// global (or TSS)
extern CDMap<uint_64t> g_hash_bool;
extern CDMap<uint_64t> g_hash_int;
extern CDMap<Expr>     g_hash_expr;
extern CDMap<void*>    g_hash_ptr;

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
  static CDMap<uint_64t> *s_hash;

  template <class Attr>
  BitAccessor& find(Expr e, const Attr&);

  template <class Attr>
  bool find(Expr e, const Attr&) const;
};

template <>
class AttrTable<uint_64t> {
public:  
  // int(egral) specialization
  static CDMap<uint64_t> *s_hash;
  uint_64t& find(x);
  uint_64t& find(x) const;
};

template <class T>
class AttrTable<T*> {
  // pointer specialization
  static CDMap<void*> *s_hash;
public:
};

template <>
class AttrTable<Expr> {
public:
  // Expr specialization
  static CDMap<Expr> *s_hash;
  find(x)
};

template <> AttrTable<bool>::s_hash     = &g_hash_bool;
template <> AttrTable<uint_64t>::s_hash = &g_hash_int;
template <> AttrTable<Expr>::s_hash     = &g_hash_expr;
template <> AttrTable<void*>::s_hash    = &g_hash_ptr;

template <class Attr>
class AttributeTable {
  typedef typename Attr::value_type value_type;

  AttrTable<value_type>& d_table;
  
};

} /* CVC4 namespace */

#endif /* __CVC4_EXPR_ATTRIBUTE_H */
