/*********************                                                        */
/** node.h
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Reference-counted encapsulation of a pointer to node information.
 **/

#include "expr/node_value.h"

#ifndef __CVC4__NODE_H
#define __CVC4__NODE_H

#include <vector>
#include <string>
#include <iostream>
#include <stdint.h>

#include "cvc4_config.h"
#include "expr/kind.h"
#include "expr/type.h"
#include "util/Assert.h"

namespace CVC4 {

template<bool ref_count>
  class NodeTemplate;
typedef NodeTemplate<true> Node;
typedef NodeTemplate<false> TNode;

inline std::ostream& operator<<(std::ostream&, const Node&);

class NodeManager;
class Type;

namespace expr {
class NodeValue;
}/* CVC4::expr namespace */

using CVC4::expr::NodeValue;

/**
 * Encapsulation of an NodeValue pointer.  The reference count is
 * maintained in the NodeValue.
 */
template<bool ref_count>
  class NodeTemplate {

  friend class NodeValue;

    /** A convenient null-valued encapsulated pointer */
    static NodeTemplate s_null;

    /** The referenced NodeValue */
    NodeValue* d_ev;

    bool d_count_ref;

    /** This constructor is reserved for use by the NodeTemplate package; one
     *  must construct an NodeTemplate using one of the build mechanisms of the
     *  NodeTemplate package.
     *
     *  Increments the reference count.
     *
     *  FIXME: there's a type-system escape here to cast away the const,
     *  since the refcount needs to be updated.  But conceptually Nodes
     *  don't change their arguments, and it's nice to have
     *  const_iterators over them.  See notes in .cpp file for
     *  details. */
    // this really does needs to be explicit to avoid hard to track
    // errors with Nodes implicitly wrapping NodeValues
    explicit NodeTemplate(const NodeValue*);

    template<unsigned>
      friend class NodeBuilder;

    friend class NodeTemplate<true>;
    friend class NodeTemplate<false>;

    friend class NodeManager;

    /**
     * Assigns the expression value and does reference counting. No assumptions
     * are made on the expression, and should only be used if we know what we are
     * doing.
     *
     * @param ev the expression value to assign
     */
    void assignNodeValue(NodeValue* ev);

    typedef NodeValue::ev_iterator ev_iterator;
    typedef NodeValue::const_ev_iterator const_ev_iterator;

    inline ev_iterator ev_begin();
    inline ev_iterator ev_end();
    inline const_ev_iterator ev_begin() const;
    inline const_ev_iterator ev_end() const;

  public:

    /** Default constructor, makes a null expression. */
    NodeTemplate();

    NodeTemplate operator[](int i) const {
      Assert(i >= 0 && unsigned(i) < d_ev->d_nchildren);
      return NodeTemplate(d_ev->d_children[i]);
    }

    template <bool ref_count_1>
    NodeTemplate(const NodeTemplate<ref_count_1>&);

    /** Destructor.  Decrements the reference count and, if zero,
     *  collects the NodeValue. */
    ~NodeTemplate();

    bool operator==(const NodeTemplate& e) const {
      return d_ev == e.d_ev;
    }
    bool operator!=(const NodeTemplate& e) const {
      return d_ev != e.d_ev;
    }

    /**
     * We compare by expression ids so, keeping things deterministic and having
     * that subexpressions have to be smaller than the enclosing expressions.
     */
    inline bool operator<(const NodeTemplate& e) const;

    template <bool ref_count_1>
    NodeTemplate& operator=(const NodeTemplate<ref_count_1>&);

    size_t hash() const {
      return d_ev->getId();
    }

    uint64_t getId() const {
      return d_ev->getId();
    }

    const Type* getType() const;

    NodeTemplate eqExpr(const NodeTemplate& right) const;
    NodeTemplate notExpr() const;
    NodeTemplate andExpr(const NodeTemplate& right) const;
    NodeTemplate orExpr(const NodeTemplate& right) const;
    NodeTemplate iteExpr(const NodeTemplate& thenpart,
                         const NodeTemplate& elsepart) const;
    NodeTemplate iffExpr(const NodeTemplate& right) const;
    NodeTemplate impExpr(const NodeTemplate& right) const;
    NodeTemplate xorExpr(const NodeTemplate& right) const;

    NodeTemplate plusExpr(const NodeTemplate& right) const;
    NodeTemplate uMinusExpr() const;
    NodeTemplate multExpr(const NodeTemplate& right) const;

    inline Kind getKind() const;

    inline size_t getNumChildren() const;


    static NodeTemplate null();

    typedef typename NodeValue::iterator<ref_count> iterator;
    typedef typename NodeValue::iterator<ref_count> const_iterator;

    inline iterator begin();
    inline iterator end();
    inline const_iterator begin() const;
    inline const_iterator end() const;

    template <class AttrKind>
    inline typename AttrKind::value_type getAttribute(const AttrKind&) const;

    template <class AttrKind>
    inline bool hasAttribute(const AttrKind&, typename AttrKind::value_type* = NULL) const;

    inline std::string toString() const;
    inline void toStream(std::ostream&) const;


    bool isNull() const;
    bool isAtomic() const;

  /**
   * Very basic pretty printer for Node.
   * @param o output stream to print to.
   * @param indent number of spaces to indent the formula by.
   */
  void printAst(std::ostream & o, int indent = 0) const;

private:

  /**
   * Pretty printer for use within gdb
   * This is not intended to be used outside of gdb.
   * This writes to the ostream Warning() and immediately flushes
   * the ostream.
   */
  void debugPrint();

  template<class AttrKind>
  inline void setAttribute(
      const AttrKind&, const typename AttrKind::value_type& value);

    static void indent(std::ostream & o, int indent) {
      for(int i = 0; i < indent; i++)
        o << ' ';
    }

  };/* class NodeTemplate */

}/* CVC4 namespace */

#include <ext/hash_map>

// for hashtables
namespace __gnu_cxx {
template<>
  struct hash<CVC4::Node> {
    size_t operator()(const CVC4::Node& node) const {
      return (size_t) node.hash();
    }
  };
}/* __gnu_cxx namespace */

#include "expr/attribute.h"
#include "expr/node_manager.h"

namespace CVC4 {

template<bool ref_count>
  inline bool NodeTemplate<ref_count>::operator<(const NodeTemplate& e) const {
    return d_ev->d_id < e.d_ev->d_id;
  }

inline std::ostream& operator<<(std::ostream& out, const Node& e) {
  e.toStream(out);
  return out;
}

template<bool ref_count>
  inline Kind NodeTemplate<ref_count>::getKind() const {
    return Kind(d_ev->d_kind);
  }

template<bool ref_count>
  inline std::string NodeTemplate<ref_count>::toString() const {
    return d_ev->toString();
  }

template<bool ref_count>
  inline void NodeTemplate<ref_count>::toStream(std::ostream& out) const {
    d_ev->toStream(out);
  }

template<bool ref_count>
  inline typename NodeTemplate<ref_count>::ev_iterator NodeTemplate<ref_count>::ev_begin() {
    return d_ev->ev_begin();
  }

template<bool ref_count>
  inline typename NodeTemplate<ref_count>::ev_iterator NodeTemplate<ref_count>::ev_end() {
    return d_ev->ev_end();
  }

template<bool ref_count>
  inline typename NodeTemplate<ref_count>::const_ev_iterator NodeTemplate<
      ref_count>::ev_begin() const {
    return d_ev->ev_begin();
  }

template<bool ref_count>
  inline typename NodeTemplate<ref_count>::const_ev_iterator NodeTemplate<
      ref_count>::ev_end() const {
    return d_ev->ev_end();
  }

template<bool ref_count>
  inline typename NodeTemplate<ref_count>::iterator NodeTemplate<ref_count>::begin() {
    return d_ev->begin<ref_count> ();
  }

template<bool ref_count>
  inline typename NodeTemplate<ref_count>::iterator NodeTemplate<ref_count>::end() {
    return d_ev->end<ref_count> ();
  }

template<bool ref_count>
  inline typename NodeTemplate<ref_count>::const_iterator NodeTemplate<
      ref_count>::begin() const {
    return d_ev->begin<ref_count> ();
  }

template<bool ref_count>
  inline typename NodeTemplate<ref_count>::const_iterator NodeTemplate<
      ref_count>::end() const {
    return d_ev->end<ref_count> ();
  }

template<bool ref_count>
  inline size_t NodeTemplate<ref_count>::getNumChildren() const {
    return d_ev->d_nchildren;
  }

template <bool ref_count>
template <class AttrKind>
inline typename AttrKind::value_type NodeTemplate<ref_count>::getAttribute(const AttrKind&) const {
  Assert( NodeManager::currentNM() != NULL,
          "There is no current CVC4::NodeManager associated to this thread.\n"
          "Perhaps a public-facing function is missing a NodeManagerScope ?" );

  return NodeManager::currentNM()->getAttribute(*this, AttrKind());
}

template <bool ref_count>
template <class AttrKind>
inline bool NodeTemplate<ref_count>::hasAttribute(const AttrKind&,
                               typename AttrKind::value_type* ret) const {
  Assert( NodeManager::currentNM() != NULL,
          "There is no current CVC4::NodeManager associated to this thread.\n"
          "Perhaps a public-facing function is missing a NodeManagerScope ?" );

  return NodeManager::currentNM()->hasAttribute(*this, AttrKind(), ret);
}

template <bool ref_count>
template <class AttrKind>
inline void NodeTemplate<ref_count>::setAttribute(const AttrKind&,
                               const typename AttrKind::value_type& value) {
  Assert( NodeManager::currentNM() != NULL,
          "There is no current CVC4::NodeManager associated to this thread.\n"
          "Perhaps a public-facing function is missing a NodeManagerScope ?" );

  NodeManager::currentNM()->setAttribute(*this, AttrKind(), value);
}

template<bool ref_count>
  NodeTemplate<ref_count> NodeTemplate<ref_count>::s_null(&NodeValue::s_null);

template<bool ref_count>
  NodeTemplate<ref_count> NodeTemplate<ref_count>::null() {
    return s_null;
  }

template<bool ref_count>
  bool NodeTemplate<ref_count>::isNull() const {
    return d_ev == &NodeValue::s_null;
  }

////FIXME: This function is a major hack! Should be changed ASAP
////TODO: Should use positive definition, i.e. what kinds are atomic.
template<bool ref_count>
  bool NodeTemplate<ref_count>::isAtomic() const {
    switch(getKind()) {
    case NOT:
    case XOR:
    case ITE:
    case IFF:
    case IMPLIES:
    case OR:
    case AND:
      return false;
    default:
      return true;
    }
  }

template<bool ref_count>
  NodeTemplate<ref_count>::NodeTemplate() :
    d_ev(&NodeValue::s_null) {
    // No refcount needed
  }

// FIXME: escape from type system convenient but is there a better
// way?  Nodes conceptually don't change their expr values but of
// course they do modify the refcount.  But it's nice to be able to
// support node_iterators over const NodeValue*.  So.... hm.
template<bool ref_count>
  NodeTemplate<ref_count>::NodeTemplate(const NodeValue* ev) :
    d_ev(const_cast<NodeValue*> (ev)) {
    Assert(d_ev != NULL, "Expecting a non-NULL expression value!");
    if(ref_count)
      d_ev->inc();
  }

template<bool ref_count>
template<bool ref_count_1>
  NodeTemplate<ref_count>::NodeTemplate(const NodeTemplate<ref_count_1>& e) {
    Assert(e.d_ev != NULL, "Expecting a non-NULL expression value!");
    d_ev = e.d_ev;
    if(ref_count)
      d_ev->inc();
  }

template<bool ref_count>
  NodeTemplate<ref_count>::~NodeTemplate() {
    Assert(d_ev != NULL, "Expecting a non-NULL expression value!");
    if(ref_count)
      d_ev->dec();
    Assert(ref_count || d_ev->d_rc > 0,
        "Temporary node pointing to an expired node");
  }

template<bool ref_count>
  void NodeTemplate<ref_count>::assignNodeValue(NodeValue* ev) {
    d_ev = ev;
    if(ref_count)
      d_ev->inc();
  }

template<bool ref_count>
template<bool ref_count_1>
  NodeTemplate<ref_count>& NodeTemplate<ref_count>::operator=
      (const NodeTemplate<ref_count_1>& e) {
    Assert(d_ev != NULL, "Expecting a non-NULL expression value!");
    Assert(e.d_ev != NULL, "Expecting a non-NULL expression value on RHS!");
    if(EXPECT_TRUE( d_ev != e.d_ev )) {
      if(ref_count)
        d_ev->dec();
      d_ev = e.d_ev;
      if(ref_count)
        d_ev->inc();
    }
    return *this;
  }

template<bool ref_count>
  NodeTemplate<ref_count> NodeTemplate<ref_count>::eqExpr(const NodeTemplate<
      ref_count>& right) const {
    return NodeManager::currentNM()->mkNode(EQUAL, *this, right);
  }

template<bool ref_count>
  NodeTemplate<ref_count> NodeTemplate<ref_count>::notExpr() const {
    return NodeManager::currentNM()->mkNode(NOT, *this);
  }

template<bool ref_count>
  NodeTemplate<ref_count> NodeTemplate<ref_count>::andExpr(
      const NodeTemplate<ref_count>& right) const {
    return NodeManager::currentNM()->mkNode(AND, *this, right);
  }

template<bool ref_count>
  NodeTemplate<ref_count> NodeTemplate<ref_count>::orExpr(
      const NodeTemplate<ref_count>& right) const {
    return NodeManager::currentNM()->mkNode(OR, *this, right);
  }

template<bool ref_count>
  NodeTemplate<ref_count> NodeTemplate<ref_count>::iteExpr(
      const NodeTemplate<ref_count>& thenpart,
      const NodeTemplate<ref_count>& elsepart) const {
    return NodeManager::currentNM()->mkNode(ITE, *this, thenpart, elsepart);
  }

template<bool ref_count>
  NodeTemplate<ref_count> NodeTemplate<ref_count>::iffExpr(
      const NodeTemplate<ref_count>& right) const {
    return NodeManager::currentNM()->mkNode(IFF, *this, right);
  }

template<bool ref_count>
  NodeTemplate<ref_count> NodeTemplate<ref_count>::impExpr(
      const NodeTemplate<ref_count>& right) const {
    return NodeManager::currentNM()->mkNode(IMPLIES, *this, right);
  }

template<bool ref_count>
  NodeTemplate<ref_count> NodeTemplate<ref_count>::xorExpr(
      const NodeTemplate<ref_count>& right) const {
    return NodeManager::currentNM()->mkNode(XOR, *this, right);
  }


template<bool ref_count>
  void NodeTemplate<ref_count>::printAst(std::ostream& out, int ind) const {
    indent(out, ind);
    out << '(';
    out << getKind();
    if(getKind() == VARIABLE) {
      out << ' ' << getId();

    } else if(getNumChildren() >= 1) {
      for(const_iterator child = begin(); child != end(); ++child) {
        out << std::endl;
        NodeTemplate((*child)).printAst(out, ind + 1);
      }
      out << std::endl;
      indent(out, ind);
    }
    out << ')';
  }

template<bool ref_count>
  void NodeTemplate<ref_count>::debugPrint() {
    printAst(Warning(), 0);
    Warning().flush();
  }

template<bool ref_count>
const Type* NodeTemplate<ref_count>::getType() const {
  Assert( NodeManager::currentNM() != NULL,
          "There is no current CVC4::NodeManager associated to this thread.\n"
          "Perhaps a public-facing function is missing a NodeManagerScope ?" );
  return NodeManager::currentNM()->getType(*this);
}

}/* CVC4 namespace */

#endif /* __CVC4__NODE_H */
