/*********************                                                        */
/*! \file node.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: cconway, dejan
 ** Minor contributors (to current version): taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Reference-counted encapsulation of a pointer to node information.
 **
 ** Reference-counted encapsulation of a pointer to node information.
 **/

#include "cvc4_private.h"

// circular dependency
#include "expr/node_value.h"

#ifndef __CVC4__NODE_H
#define __CVC4__NODE_H

#include <vector>
#include <string>
#include <iostream>
#include <stdint.h>

#include "type.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/expr.h"
#include "util/Assert.h"
#include "util/output.h"

namespace CVC4 {

class TypeNode;
class NodeManager;

template <bool ref_count>
class NodeTemplate;

/**
 * Exception thrown during the type-checking phase, it can be
 * thrown by node.getType().
 */
class TypeCheckingExceptionPrivate : public Exception {

private:

  /** The node repsonsible for the failure */
  NodeTemplate<true>* d_node;

protected:

  TypeCheckingExceptionPrivate(): Exception() {}

public:

  /**
   * Construct the exception with the problematic node and the message
   * @param node the problematic node
   * @param message the message explaining the failure
   */
  TypeCheckingExceptionPrivate(NodeTemplate<false> node, std::string message);

  /** Destructor */
  ~TypeCheckingExceptionPrivate() throw ();

  /**
   * Get the Node that caused the type-checking to fail.
   * @return the node
   */
  NodeTemplate<true> getNode() const;

  /** Returns the message corresponding to the type-checking failure */
  std::string toString() const;
};

/**
 * The Node class encapsulates the NodeValue with reference counting.
 */
typedef NodeTemplate<true> Node;

/**
 * The TNode class encapsulates the NodeValue but doesn't count references.
 */
typedef NodeTemplate<false> TNode;

namespace expr {

class NodeValue;

  namespace attr {
    class AttributeManager;
  }/* CVC4::expr::attr namespace */

  class ExprSetDepth;
}/* CVC4::expr namespace */

/**
 * Encapsulation of an NodeValue pointer.  The reference count is
 * maintained in the NodeValue if ref_count is true.
 * @param ref_count if true reference are counted in the NodeValue
 */
template <bool ref_count>
class NodeTemplate {

  /**
   * The NodeValue has access to the private constructors, so that the
   * iterators can can create new nodes.
   */
  friend class expr::NodeValue;

  /** A convenient null-valued encapsulated pointer */
  static NodeTemplate s_null;

  /** The referenced NodeValue */
  expr::NodeValue* d_nv;

  /**
   * This constructor is reserved for use by the NodeTemplate package; one
   * must construct an NodeTemplate using one of the build mechanisms of the
   * NodeTemplate package.
   *
   * FIXME: there's a type-system escape here to cast away the const,
   * since the refcount needs to be updated.  But conceptually Nodes
   * don't change their arguments, and it's nice to have
   * const_iterators over them.
   *
   * This really does needs to be explicit to avoid hard to track errors with
   * Nodes implicitly wrapping NodeValues
   */
  explicit NodeTemplate(const expr::NodeValue*);

  friend class NodeTemplate<true>;
  friend class NodeTemplate<false>;
  friend class NodeManager;

  template <unsigned nchild_thresh>
  friend class NodeBuilder;

  friend class ::CVC4::expr::attr::AttributeManager;

  /**
   * Assigns the expression value and does reference counting. No assumptions
   * are made on the expression, and should only be used if we know what we 
   * are doing.
   *
   * @param ev the expression value to assign
   */
  void assignNodeValue(expr::NodeValue* ev);

public:

  /** Default constructor, makes a null expression. */
  NodeTemplate() : d_nv(&expr::NodeValue::s_null) { }

  /**
   * Conversion between nodes that are reference-counted and those that are
   * not.
   * @param node the node to make copy of
   */
  NodeTemplate(const NodeTemplate<!ref_count>& node);

  /**
   * Copy constructor.  Note that GCC does NOT recognize an instantiation of
   * the above template as a copy constructor and problems ensue.  So we
   * provide an explicit one here.
   * @param node the node to make copy of
   */
  NodeTemplate(const NodeTemplate& node);

  /**
   * Assignment operator for nodes, copies the relevant information from node
   * to this node.
   * @param node the node to copy
   * @return reference to this node
   */
  NodeTemplate& operator=(const NodeTemplate& node);

  /**
   * Assignment operator for nodes, copies the relevant information from node
   * to this node.
   * @param node the node to copy
   * @return reference to this node
   */
  NodeTemplate& operator=(const NodeTemplate<!ref_count>& node);

  /**
   * Destructor. If ref_count is true it will decrement the reference count
   * and, if zero, collect the NodeValue.
   */
  ~NodeTemplate() throw(AssertionException);

  /**
   * Return the null node.
   * @return the null node
   */
  static NodeTemplate null() {
    return s_null;
  }

  /**
   * Returns true if this expression is a null expression.
   * @return true if null
   */
  bool isNull() const {
    return d_nv == &expr::NodeValue::s_null;
  }

  /**
   * Structural comparison operator for expressions.
   * @param node the node to compare to
   * @return true if expressions are equal, false otherwise
   */
  template <bool ref_count_1>
  bool operator==(const NodeTemplate<ref_count_1>& node) const {
    return d_nv == node.d_nv;
  }

  /**
   * Structural comparison operator for expressions.
   * @param node the node to compare to
   * @return false if expressions are equal, true otherwise
   */
  template <bool ref_count_1>
  bool operator!=(const NodeTemplate<ref_count_1>& node) const {
    return d_nv != node.d_nv;
  }

  /**
   * We compare by expression ids so, keeping things deterministic and having
   * that subexpressions have to be smaller than the enclosing expressions.
   * @param node the node to compare to
   * @return true if this expression is smaller
   */
  template <bool ref_count_1>
  inline bool operator<(const NodeTemplate<ref_count_1>& node) const {
    return d_nv->d_id < node.d_nv->d_id;
  }

  /**
   * Returns the i-th child of this node.
   * @param i the index of the child
   * @return the node representing the i-th child
   */
  NodeTemplate operator[](int i) const {
    if(!ref_count) {
      Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
    }
    return NodeTemplate(d_nv->getChild(i));
  }

  /* A note on isAtomic() and isAtomicFormula() (in CVC3 parlance)..
   *
   * It has been decided for now to hold off on implementations of
   * these functions, as they may only be needed in CNF conversion,
   * where it's pointless to do a lazy isAtomic determination by
   * searching through the DAG, and storing it, since the result will
   * only be used once.  For more details see the 4/27/2010 CVC4
   * developer's meeting notes at:
   *
   * http://goedel.cims.nyu.edu/wiki/Meeting_Minutes_-_April_27,_2010#isAtomic.28.29_and_isAtomicFormula.28.29
   */
  // bool containsDecision(); // is "atomic"
  // bool properlyContainsDecision(); // maybe not atomic but all children are

  /**
   * Returns true if this node represents a constant
   * @return true if const
   */
  inline bool isConst() const {
    return getMetaKind() == kind::metakind::CONSTANT;
  }

  /**
   * Returns the unique id of this node
   * @return the ud
   */
  unsigned getId() const {
    if(!ref_count) {
      Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
    }

    return d_nv->getId();
  }

  /**
   * Returns a node representing the operator of this expression.
   * If this is an APPLY, then the operator will be a functional term.
   * Otherwise, it will be a node with kind BUILTIN
   */
  NodeTemplate<true> getOperator() const;

  /** Returns true if the node has an operator (i.e., it's not a variable or a constant). */
  inline bool hasOperator() const;

  /**
   * Returns the type of this node.
   * @return the type
   */
  TypeNode getType() const
    throw (CVC4::TypeCheckingExceptionPrivate, CVC4::AssertionException);

  /**
   * Returns the kind of this node.
   * @return the kind
   */
  inline Kind getKind() const {
    if(!ref_count) {
      Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
    }

    return Kind(d_nv->d_kind);
  }

  /**
   * Returns the metakind of this node.
   * @return the metakind
   */
  inline kind::MetaKind getMetaKind() const {
    return kind::metaKindOf(getKind());
  }

  /**
   * Returns the number of children this node has.
   * @return the number of children
   */
  inline size_t getNumChildren() const;

  /**
   * If this is a CONST_* Node, extract the constant from it.
   */
  template <class T>
  inline const T& getConst() const;

  /**
   * Returns the value of the given attribute that this has been attached.
   * @param attKind the kind of the attribute
   * @return the value of the attribute
   */
  template <class AttrKind>
  inline typename AttrKind::value_type getAttribute(const AttrKind& attKind) const;

  // Note that there are two, distinct hasAttribute() declarations for
  // a reason (rather than using a pointer-valued argument with a
  // default value): they permit more optimized code in the underlying
  // hasAttribute() implementations.

  /**
   * Returns true if this node has been associated an attribute of given kind.
   * Additionaly, if a pointer to the value_kind is give, and the attribute
   * value has been set for this node, it will be returned.
   * @param attKind the kind of the attribute
   * @return true if this node has the requested attribute
   */
  template <class AttrKind>
  inline bool hasAttribute(const AttrKind& attKind) const;

  /**
   * Returns true if this node has been associated an attribute of given kind.
   * Additionaly, if a pointer to the value_kind is give, and the attribute
   * value has been set for this node, it will be returned.
   * @param attKind the kind of the attribute
   * @param value where to store the value if it exists
   * @return true if this node has the requested attribute
   */
  template <class AttrKind>
  inline bool getAttribute(const AttrKind& attKind,
                           typename AttrKind::value_type& value) const;

  /**
   * Sets the given attribute of this node to the given value.
   * @param attKind the kind of the atribute
   * @param value the value to set the attribute to
   */
  template <class AttrKind>
  inline void setAttribute(const AttrKind& attKind,
                           const typename AttrKind::value_type& value);

  /** Iterator allowing for scanning through the children. */
  typedef typename expr::NodeValue::iterator< NodeTemplate<ref_count> > iterator;
  /** Constant iterator allowing for scanning through the children. */
  typedef typename expr::NodeValue::iterator< NodeTemplate<ref_count> > const_iterator;

  /**
   * Returns the iterator pointing to the first child.
   * @return the iterator
   */
  inline iterator begin() {
    if(!ref_count) {
      Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
    }

    return d_nv->begin< NodeTemplate<ref_count> >();
  }

  /**
   * Returns the iterator pointing to the end of the children (one beyond the
   * last one.
   * @return the end of the children iterator.
   */
  inline iterator end() {
    if(!ref_count) {
      Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
    }

    return d_nv->end< NodeTemplate<ref_count> >();
  }

  /**
   * Returns the const_iterator pointing to the first child.
   * @return the const_iterator
   */
  inline const_iterator begin() const {
    if(!ref_count) {
      Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
    }

    return d_nv->begin< NodeTemplate<ref_count> >();
  }

  /**
   * Returns the const_iterator pointing to the end of the children (one
   * beyond the last one.
   * @return the end of the children const_iterator.
   */
  inline const_iterator end() const {
    if(!ref_count) {
      Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
    }

    return d_nv->end< NodeTemplate<ref_count> >();
  }

  /**
   * Converts this node into a string representation.
   * @return the string representation of this node.
   */
  inline std::string toString() const {
    if(!ref_count) {
      Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
    }

    return d_nv->toString();
  }

  /**
   * Converst this node into a string representation and sends it to the
   * given stream
   * @param out the sream to serialise this node to
   */
  inline void toStream(std::ostream& out, int toDepth = -1,
                       bool types = false) const {
    if(!ref_count) {
      Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
    }

    d_nv->toStream(out, toDepth, types);
  }

  /**
   * IOStream manipulator to set the maximum depth of Nodes when
   * pretty-printing.  -1 means print to any depth.  E.g.:
   *
   *   // let a, b, c, and d be VARIABLEs
   *   Node n = nm->mkNode(OR, a, b, nm->mkNode(AND, c, nm->mkNode(NOT, d)))
   *   out << setdepth(3) << n;
   *
   * gives "(OR a b (AND c (NOT d)))", but
   *
   *   out << setdepth(1) << [same node as above]
   *
   * gives "(OR a b (...))"
   */
  typedef expr::ExprSetDepth setdepth;

  /**
   * IOStream manipulator to print type ascriptions or not.
   *
   *   // let a, b, c, and d be variables of sort U
   *   Node n = nm->mkNode(OR, a, b, nm->mkNode(AND, c, nm->mkNode(NOT, d)))
   *   out << n;
   *
   * gives "(OR a:U b:U (AND c:U (NOT d:U)))", but
   */
  typedef expr::ExprPrintTypes printtypes;

  /**
   * Very basic pretty printer for Node.
   * @param o output stream to print to.
   * @param indent number of spaces to indent the formula by.
   */
  inline void printAst(std::ostream& out, int indent = 0) const;

  NodeTemplate<true> eqNode(const NodeTemplate& right) const;

  NodeTemplate<true> notNode() const;
  NodeTemplate<true> andNode(const NodeTemplate& right) const;
  NodeTemplate<true> orNode(const NodeTemplate& right) const;
  NodeTemplate<true> iteNode(const NodeTemplate& thenpart,
                             const NodeTemplate& elsepart) const;
  NodeTemplate<true> iffNode(const NodeTemplate& right) const;
  NodeTemplate<true> impNode(const NodeTemplate& right) const;
  NodeTemplate<true> xorNode(const NodeTemplate& right) const;

};/* class NodeTemplate<ref_count> */

/**
 * Serializes a given node to the given stream.
 * @param out the output stream to use
 * @param node the node to output to the stream
 * @return the changed stream.
 */
inline std::ostream& operator<<(std::ostream& out, TNode n) {
  n.toStream(out,
             Node::setdepth::getDepth(out),
             Node::printtypes::getPrintTypes(out));
  return out;
}

}/* CVC4 namespace */

#include <ext/hash_map>

#include "expr/attribute.h"
#include "expr/node_manager.h"

namespace CVC4 {

// for hash_maps, hash_sets..
struct NodeHashFunction {
  size_t operator()(const CVC4::Node& node) const {
    return (size_t) node.getId();
  }
};

// for hash_maps, hash_sets..
struct TNodeHashFunction {
  size_t operator()(CVC4::TNode node) const {
    return (size_t) node.getId();
  }
};

template <bool ref_count>
inline size_t NodeTemplate<ref_count>::getNumChildren() const {
  return d_nv->getNumChildren();
}

template <bool ref_count>
template <class T>
inline const T& NodeTemplate<ref_count>::getConst() const {
  return d_nv->getConst<T>();
}

template <bool ref_count>
template <class AttrKind>
inline typename AttrKind::value_type NodeTemplate<ref_count>::
getAttribute(const AttrKind&) const {
  Assert( NodeManager::currentNM() != NULL,
          "There is no current CVC4::NodeManager associated to this thread.\n"
          "Perhaps a public-facing function is missing a NodeManagerScope ?" );

  if(!ref_count) {
    Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
  }

  return NodeManager::currentNM()->getAttribute(*this, AttrKind());
}

template <bool ref_count>
template <class AttrKind>
inline bool NodeTemplate<ref_count>::
hasAttribute(const AttrKind&) const {
  Assert( NodeManager::currentNM() != NULL,
          "There is no current CVC4::NodeManager associated to this thread.\n"
          "Perhaps a public-facing function is missing a NodeManagerScope ?" );

  if(!ref_count) {
    Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
  }

  return NodeManager::currentNM()->hasAttribute(*this, AttrKind());
}

template <bool ref_count>
template <class AttrKind>
inline bool NodeTemplate<ref_count>::getAttribute(const AttrKind&,
                                                  typename AttrKind::value_type& ret) const {
  Assert( NodeManager::currentNM() != NULL,
          "There is no current CVC4::NodeManager associated to this thread.\n"
          "Perhaps a public-facing function is missing a NodeManagerScope ?" );

  if(!ref_count) {
    Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
  }

  return NodeManager::currentNM()->getAttribute(*this, AttrKind(), ret);
}

template <bool ref_count>
template <class AttrKind>
inline void NodeTemplate<ref_count>::
setAttribute(const AttrKind&, const typename AttrKind::value_type& value) {
  Assert( NodeManager::currentNM() != NULL,
          "There is no current CVC4::NodeManager associated to this thread.\n"
          "Perhaps a public-facing function is missing a NodeManagerScope ?" );

  if(!ref_count) {
    Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
  }

  NodeManager::currentNM()->setAttribute(*this, AttrKind(), value);
}

template <bool ref_count>
NodeTemplate<ref_count> NodeTemplate<ref_count>::s_null(&expr::NodeValue::s_null);

// FIXME: escape from type system convenient but is there a better
// way?  Nodes conceptually don't change their expr values but of
// course they do modify the refcount.  But it's nice to be able to
// support node_iterators over const NodeValue*.  So.... hm.
template <bool ref_count>
NodeTemplate<ref_count>::NodeTemplate(const expr::NodeValue* ev) :
  d_nv(const_cast<expr::NodeValue*> (ev)) {
  Assert(d_nv != NULL, "Expecting a non-NULL expression value!");
  if(ref_count) {
    d_nv->inc();
  } else {
    Assert(d_nv->d_rc > 0, "TNode constructed from NodeValue with rc == 0");
  }
}

// the code for these two following constructors ("conversion/copy
// constructors") is identical, but we need both.  see comment in the
// class.

template <bool ref_count>
NodeTemplate<ref_count>::NodeTemplate(const NodeTemplate<!ref_count>& e) {
  Assert(e.d_nv != NULL, "Expecting a non-NULL expression value!");
  d_nv = e.d_nv;
  if(ref_count) {
    d_nv->inc();
  } else {
    // shouldn't ever happen
    Assert(d_nv->d_rc > 0,
           "TNode constructed from Node with rc == 0");
  }
}

template <bool ref_count>
NodeTemplate<ref_count>::NodeTemplate(const NodeTemplate& e) {
  Assert(e.d_nv != NULL, "Expecting a non-NULL expression value!");
  d_nv = e.d_nv;
  if(ref_count) {
    d_nv->inc();
  } else {
    Assert(d_nv->d_rc > 0, "TNode constructed from TNode with rc == 0");
  }
}

template <bool ref_count>
NodeTemplate<ref_count>::~NodeTemplate() throw(AssertionException) {
  Assert(d_nv != NULL, "Expecting a non-NULL expression value!");
  if(ref_count) {
    d_nv->dec();
  } else {
    Assert(d_nv->d_rc > 0 || d_nv->isBeingDeleted() || NodeManager::currentNM()->inDestruction(),
           "TNode pointing to an expired NodeValue at destruction time");
  }
}

template <bool ref_count>
void NodeTemplate<ref_count>::assignNodeValue(expr::NodeValue* ev) {
  d_nv = ev;
  if(ref_count) {
    d_nv->inc();
  } else {
    Assert(d_nv->d_rc > 0, "TNode assigned to NodeValue with rc == 0");
  }
}

template <bool ref_count>
NodeTemplate<ref_count>& NodeTemplate<ref_count>::
operator=(const NodeTemplate& e) {
  Assert(d_nv != NULL, "Expecting a non-NULL expression value!");
  Assert(e.d_nv != NULL, "Expecting a non-NULL expression value on RHS!");
  if(EXPECT_TRUE( d_nv != e.d_nv )) {
    if(ref_count) {
      d_nv->dec();
    }
    d_nv = e.d_nv;
    if(ref_count) {
      d_nv->inc();
    } else {
      Assert(d_nv->d_rc > 0, "TNode assigned from TNode with rc == 0");
    }
  }
  return *this;
}

template <bool ref_count>
NodeTemplate<ref_count>& NodeTemplate<ref_count>::
operator=(const NodeTemplate<!ref_count>& e) {
  Assert(d_nv != NULL, "Expecting a non-NULL expression value!");
  Assert(e.d_nv != NULL, "Expecting a non-NULL expression value on RHS!");
  if(EXPECT_TRUE( d_nv != e.d_nv )) {
    if(ref_count) {
      d_nv->dec();
    }
    d_nv = e.d_nv;
    if(ref_count) {
      d_nv->inc();
    } else {
      // shouldn't ever happen
      Assert(d_nv->d_rc > 0,
             "TNode assigned from Node with rc == 0");
    }
  }
  return *this;
}

template <bool ref_count>
NodeTemplate<true>
NodeTemplate<ref_count>::eqNode(const NodeTemplate<ref_count>& right) const {
  if(!ref_count) {
    Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
  }

  return NodeManager::currentNM()->mkNode(kind::EQUAL, *this, right);
}

template <bool ref_count>
NodeTemplate<true> NodeTemplate<ref_count>::notNode() const {
  if(!ref_count) {
    Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
  }

  return NodeManager::currentNM()->mkNode(kind::NOT, *this);
}

template <bool ref_count>
NodeTemplate<true>
NodeTemplate<ref_count>::andNode(const NodeTemplate<ref_count>& right) const {
  if(!ref_count) {
    Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
  }

  return NodeManager::currentNM()->mkNode(kind::AND, *this, right);
}

template <bool ref_count>
NodeTemplate<true>
NodeTemplate<ref_count>::orNode(const NodeTemplate<ref_count>& right) const {
  if(!ref_count) {
    Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
  }

  return NodeManager::currentNM()->mkNode(kind::OR, *this, right);
}

template <bool ref_count>
NodeTemplate<true>
NodeTemplate<ref_count>::iteNode(const NodeTemplate<ref_count>& thenpart,
                                 const NodeTemplate<ref_count>& elsepart) const {
  if(!ref_count) {
    Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
  }

  return NodeManager::currentNM()->mkNode(kind::ITE, *this, thenpart, elsepart);
}

template <bool ref_count>
NodeTemplate<true>
NodeTemplate<ref_count>::iffNode(const NodeTemplate<ref_count>& right) const {
  if(!ref_count) {
    Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
  }

  return NodeManager::currentNM()->mkNode(kind::IFF, *this, right);
}

template <bool ref_count>
NodeTemplate<true>
NodeTemplate<ref_count>::impNode(const NodeTemplate<ref_count>& right) const {
  if(!ref_count) {
    Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
  }

  return NodeManager::currentNM()->mkNode(kind::IMPLIES, *this, right);
}

template <bool ref_count>
NodeTemplate<true>
NodeTemplate<ref_count>::xorNode(const NodeTemplate<ref_count>& right) const {
  if(!ref_count) {
    Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
  }

  return NodeManager::currentNM()->mkNode(kind::XOR, *this, right);
}

template <bool ref_count>
inline void
NodeTemplate<ref_count>::printAst(std::ostream& out, int indent) const {
  d_nv->printAst(out, indent);
}

/**
 * Returns a node representing the operator of this expression.
 * If this is an APPLY, then the operator will be a functional term.
 * Otherwise, it will be a node with kind BUILTIN
 */
template <bool ref_count>
NodeTemplate<true> NodeTemplate<ref_count>::getOperator() const {
  Assert( NodeManager::currentNM() != NULL,
          "There is no current CVC4::NodeManager associated to this thread.\n"
          "Perhaps a public-facing function is missing a NodeManagerScope ?" );

  if(!ref_count) {
    Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
  }

  switch(kind::MetaKind mk = getMetaKind()) {
  case kind::metakind::INVALID:
    IllegalArgument(*this, "getOperator() called on Node with INVALID-kinded kind");

  case kind::metakind::VARIABLE:
    IllegalArgument(*this, "getOperator() called on Node with VARIABLE-kinded kind");

  case kind::metakind::OPERATOR: {
    /* Returns a BUILTIN node. */
    return NodeManager::currentNM()->operatorOf(getKind());
  }

  case kind::metakind::PARAMETERIZED:
    /* The operator is the first child. */
    return Node(d_nv->d_children[0]);

  case kind::metakind::CONSTANT:
    IllegalArgument(*this, "getOperator() called on Node with CONSTANT-kinded kind");

  default:
    Unhandled(mk);
  }
}

/**
 * Returns true if the node has an operator (i.e., it's not a variable
 * or a constant).
 */
template <bool ref_count>
inline bool NodeTemplate<ref_count>::hasOperator() const {
  return NodeManager::hasOperator(getKind());
}

template <bool ref_count>
TypeNode NodeTemplate<ref_count>::getType() const
  throw (CVC4::TypeCheckingExceptionPrivate, CVC4::AssertionException) {
  Assert( NodeManager::currentNM() != NULL,
          "There is no current CVC4::NodeManager associated to this thread.\n"
          "Perhaps a public-facing function is missing a NodeManagerScope ?" );

  if(!ref_count) {
    Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
  }

  return NodeManager::currentNM()->getType(*this);
}

#ifdef CVC4_DEBUG
/**
 * Pretty printer for use within gdb.  This is not intended to be used
 * outside of gdb.  This writes to the Warning() stream and immediately
 * flushes the stream.
 *
 * Note that this function cannot be a template, since the compiler
 * won't instantiate it.  Even if we explicitly instantiate.  (Odd?)
 * So we implement twice.  We mark as __attribute__((used)) so that
 * GCC emits code for it even though static analysis indicates it's
 * never called.
 *
 * Tim's Note: I moved this into the node.h file because this allows gdb
 * to find the symbol, and use it, which is the first standard this code needs
 * to meet. A cleaner solution is welcomed.
 */
static void __attribute__((used)) debugPrintNode(const NodeTemplate<true>& n) {
  Warning() << Node::setdepth(-1) << n << std::endl;
  Warning().flush();
}
static void __attribute__((used)) debugPrintRawNode(const NodeTemplate<true>& n) {
  n.printAst(Warning(), 0);
  Warning().flush();
}

static void __attribute__((used)) debugPrintTNode(const NodeTemplate<false>& n) {
  Warning() << Node::setdepth(-1) << n << std::endl;
  Warning().flush();
}
static void __attribute__((used)) debugPrintRawTNode(const NodeTemplate<false>& n) {
  n.printAst(Warning(), 0);
  Warning().flush();
}
#endif /* CVC4_DEBUG */

}/* CVC4 namespace */

#endif /* __CVC4__NODE_H */
