/*********************                                                        */
/*! \file node.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Reference-counted encapsulation of a pointer to node information
 **
 ** Reference-counted encapsulation of a pointer to node information.
 **/

#include "cvc4_private.h"

// circular dependency
#include "expr/node_value.h"

#ifndef __CVC4__NODE_H
#define __CVC4__NODE_H

#include <stdint.h>

#include <algorithm>
#include <functional>
#include <iostream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "base/configuration.h"
#include "base/cvc4_assert.h"
#include "base/exception.h"
#include "base/output.h"
#include "expr/type.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/expr.h"
#include "expr/expr_iomanip.h"
#include "options/language.h"
#include "options/set_language.h"
#include "util/hash.h"
#include "util/utility.h"

namespace CVC4 {

class TypeNode;
class NodeManager;

namespace expr {
  namespace pickle {
    class PicklerPrivate;
  }/* CVC4::expr::pickle namespace */
}/* CVC4::expr namespace */

template <bool ref_count>
class NodeTemplate;

/**
 * Exception thrown during the type-checking phase, it can be
 * thrown by node.getType().
 */
class TypeCheckingExceptionPrivate : public Exception {
 private:
  /** The node responsible for the failure */
  NodeTemplate<true>* d_node;

 public:
  /**
   * Construct the exception with the problematic node and the message
   * @param node the problematic node
   * @param message the message explaining the failure
   */
  TypeCheckingExceptionPrivate(NodeTemplate<false> node, std::string message);

  /** Destructor */
  ~TypeCheckingExceptionPrivate() override;

  /**
   * Get the Node that caused the type-checking to fail.
   * @return the node
   */
  NodeTemplate<true> getNode() const;

  /**
   * Returns the message corresponding to the type-checking failure.
   * We prefer toStream() to toString() because that keeps the expr-depth
   * and expr-language settings present in the stream.
   */
  void toStream(std::ostream& out) const override;

};/* class TypeCheckingExceptionPrivate */

class UnknownTypeException : public TypeCheckingExceptionPrivate {
 public:
  UnknownTypeException(NodeTemplate<false> node);
};/* class UnknownTypeException */

/**
 * \typedef NodeTemplate<true> Node;
 *
 * The Node class encapsulates the NodeValue with reference counting.
 *
 * One should use generally use Nodes to manipulate expressions, to be safe.
 * Every outstanding Node that references a NodeValue is counted in that
 * NodeValue's reference count.  Reference counts are maintained correctly
 * on assignment of the Node object (to point to another NodeValue), and,
 * upon destruction of the Node object, the NodeValue's reference count is
 * decremented and, if zero, it becomes eligible for reclamation by the
 * system.
 */
typedef NodeTemplate<true> Node;

/**
 * \typedef NodeTemplate<false> TNode;
 *
 * The TNode class encapsulates the NodeValue but doesn't count references.
 *
 * TNodes are just like Nodes, but they don't update the reference count.
 * Therefore, there is less overhead (copying a TNode is just the cost of
 * the underlying pointer copy).  Generally speaking, this is unsafe!
 * However, there are certain situations where a TNode can be used safely.
 *
 * The largest class of uses for TNodes are when you need to use them in a
 * "temporary," scoped fashion (hence the "T" in "TNode").  In general,
 * it is safe to use TNode as a function parameter type, since the calling
 * function (or some other function on the call stack) presumably has a Node
 * reference to the expression data.  It is generally _not_ safe, however,
 * to return a TNode _from_ a function.  (Functions that return Nodes often
 * create the expression they return; such new expressions may not be
 * referenced on the call stack, and have a reference count of 1 on
 * creation.  If this is returned as a TNode rather than a Node, the
 * count drops to zero, marking the expression as eligible for reclamation.)
 *
 * More guidelines on when to use TNodes is available in the CVC4
 * Developer's Guide:
 * http://goedel.cims.nyu.edu/wiki/Developer%27s_Guide#Dealing_with_expressions_.28Nodes_and_TNodes.29
 */
typedef NodeTemplate<false> TNode;

namespace expr {

class NodeValue;

  namespace attr {
    class AttributeManager;
    struct SmtAttributes;
  }/* CVC4::expr::attr namespace */

  class ExprSetDepth;
}/* CVC4::expr namespace */

namespace kind {
  namespace metakind {
    struct NodeValueConstPrinter;
  }/* CVC4::kind::metakind namespace */
}/* CVC4::kind namespace */

// for hash_maps, hash_sets..
struct NodeHashFunction {
  inline size_t operator()(Node node) const;
};/* struct NodeHashFunction */
struct TNodeHashFunction {
  inline size_t operator()(TNode node) const;
};/* struct TNodeHashFunction */

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

  friend class expr::pickle::PicklerPrivate;
  friend class expr::ExportPrivate;

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
  friend class TypeNode;
  friend class NodeManager;

  template <unsigned nchild_thresh>
  friend class NodeBuilder;

  friend class ::CVC4::expr::attr::AttributeManager;
  friend struct ::CVC4::expr::attr::SmtAttributes;

  friend struct ::CVC4::kind::metakind::NodeValueConstPrinter;

  /**
   * Assigns the expression value and does reference counting. No assumptions
   * are made on the expression, and should only be used if we know what we
   * are doing.
   *
   * @param ev the expression value to assign
   */
  void assignNodeValue(expr::NodeValue* ev);

  // May throw an AssertionException if the Node is not live, i.e. the ref count
  // is not positive.
  inline void assertTNodeNotExpired() const
  {
    if(!ref_count) {
      Assert( d_nv->d_rc > 0, "TNode pointing to an expired NodeValue" );
    }
  }

public:

  /**
   * Cache-aware, recursive version of substitute() used by the public
   * member function with a similar signature.
   */
  Node substitute(TNode node, TNode replacement,
                  std::unordered_map<TNode, TNode, TNodeHashFunction>& cache) const;

  /**
   * Cache-aware, recursive version of substitute() used by the public
   * member function with a similar signature.
   */
  template <class Iterator1, class Iterator2>
  Node substitute(Iterator1 nodesBegin, Iterator1 nodesEnd,
                  Iterator2 replacementsBegin, Iterator2 replacementsEnd,
                  std::unordered_map<TNode, TNode, TNodeHashFunction>& cache) const;

  /**
   * Cache-aware, recursive version of substitute() used by the public
   * member function with a similar signature.
   */
  template <class Iterator>
  Node substitute(Iterator substitutionsBegin, Iterator substitutionsEnd,
                  std::unordered_map<TNode, TNode, TNodeHashFunction>& cache) const;

  /** Default constructor, makes a null expression. */
  NodeTemplate() : d_nv(&expr::NodeValue::null()) { }

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
   * Allow Exprs to become Nodes.  This permits flexible translation of
   * Exprs -> Nodes inside the CVC4 library without exposing a toNode()
   * function in the public interface, or requiring lots of "friend"
   * relationships.
   */
  NodeTemplate(const Expr& e);

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
  ~NodeTemplate();

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
    assertTNodeNotExpired();
    return d_nv == &expr::NodeValue::null();
  }

  /**
   * Structural comparison operator for expressions.
   * @param node the node to compare to
   * @return true if expressions are equal, false otherwise
   */
  template <bool ref_count_1>
  bool operator==(const NodeTemplate<ref_count_1>& node) const {
    assertTNodeNotExpired();
    node.assertTNodeNotExpired();
    return d_nv == node.d_nv;
  }

  /**
   * Structural comparison operator for expressions.
   * @param node the node to compare to
   * @return false if expressions are equal, true otherwise
   */
  template <bool ref_count_1>
  bool operator!=(const NodeTemplate<ref_count_1>& node) const {
    assertTNodeNotExpired();
    node.assertTNodeNotExpired();
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
    assertTNodeNotExpired();
    node.assertTNodeNotExpired();
    return d_nv->d_id < node.d_nv->d_id;
  }

  /**
   * We compare by expression ids so, keeping things deterministic and having
   * that subexpressions have to be smaller than the enclosing expressions.
   * @param node the node to compare to
   * @return true if this expression is greater
   */
  template <bool ref_count_1>
  inline bool operator>(const NodeTemplate<ref_count_1>& node) const {
    assertTNodeNotExpired();
    node.assertTNodeNotExpired();
    return d_nv->d_id > node.d_nv->d_id;
  }

  /**
   * We compare by expression ids so, keeping things deterministic and having
   * that subexpressions have to be smaller than the enclosing expressions.
   * @param node the node to compare to
   * @return true if this expression is smaller than or equal to
   */
  template <bool ref_count_1>
  inline bool operator<=(const NodeTemplate<ref_count_1>& node) const {
    assertTNodeNotExpired();
    node.assertTNodeNotExpired();
    return d_nv->d_id <= node.d_nv->d_id;
  }

  /**
   * We compare by expression ids so, keeping things deterministic and having
   * that subexpressions have to be smaller than the enclosing expressions.
   * @param node the node to compare to
   * @return true if this expression is greater than or equal to
   */
  template <bool ref_count_1>
  inline bool operator>=(const NodeTemplate<ref_count_1>& node) const {
    assertTNodeNotExpired();
    node.assertTNodeNotExpired();
    return d_nv->d_id >= node.d_nv->d_id;
  }

  /**
   * Returns the i-th child of this node.
   * @param i the index of the child
   * @return the node representing the i-th child
   */
  NodeTemplate operator[](int i) const {
    assertTNodeNotExpired();
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
   * Returns true iff this node contains a bound variable.  This bound
   * variable may or may not be free.
   * @return true iff this node contains a bound variable.
   */
  bool hasBoundVar();

  /**
   * Convert this Node into an Expr using the currently-in-scope
   * manager.  Essentially this is like an "operator Expr()" but we
   * don't want it to compete with implicit conversions between e.g.
   * Node and TNode, and we want internal-to-external interface
   * (Node -> Expr) points to be explicit.  We could write an
   * explicit Expr(Node) constructor---but that dirties the public
   * interface.
   */
  inline Expr toExpr() const;

  /**
   * Convert an Expr into a Node.
   */
  static inline Node fromExpr(const Expr& e);

  /**
   * Returns true if this node represents a constant
   * @return true if const
   */
  bool isConst() const;

  /**
   * Returns true if this node represents a variable
   * @return true if variable
   */
  inline bool isVar() const {
    assertTNodeNotExpired();
    return getMetaKind() == kind::metakind::VARIABLE;
  }
  
  /**
   * Returns true if this node represents a nullary operator
   */
  inline bool isNullaryOp() const {
    assertTNodeNotExpired();
    return getMetaKind() == kind::metakind::NULLARY_OPERATOR;
  }
  
  inline bool isClosure() const {
    assertTNodeNotExpired();
    return getKind() == kind::LAMBDA ||
           getKind() == kind::FORALL ||
           getKind() == kind::EXISTS ||
           getKind() == kind::REWRITE_RULE;
  }

  /**
   * Returns the unique id of this node
   * @return the ud
   */
  unsigned long getId() const {
    assertTNodeNotExpired();
    return d_nv->getId();
  }

  /**
   * Returns a node representing the operator of this expression.
   * If this is an APPLY, then the operator will be a functional term.
   * Otherwise, it will be a node with kind BUILTIN.
   */
  NodeTemplate<true> getOperator() const;

  /**
   * Returns true if the node has an operator (i.e., it's not a
   * variable or a constant).
   */
  inline bool hasOperator() const;

  /**
   * Get the type for the node and optionally do type checking.
   *
   * Initial type computation will be near-constant time if
   * type checking is not requested. Results are memoized, so that
   * subsequent calls to getType() without type checking will be
   * constant time.
   *
   * Initial type checking is linear in the size of the expression.
   * Again, the results are memoized, so that subsequent calls to
   * getType(), with or without type checking, will be constant
   * time.
   *
   * NOTE: A TypeCheckingException can be thrown even when type
   * checking is not requested. getType() will always return a
   * valid and correct type and, thus, an exception will be thrown
   * when no valid or correct type can be computed (e.g., if the
   * arguments to a bit-vector operation aren't bit-vectors). When
   * type checking is not requested, getType() will do the minimum
   * amount of checking required to return a valid result.
   *
   * @param check whether we should check the type as we compute it
   * (default: false)
   */
  TypeNode getType(bool check = false) const;

  /**
   * Substitution of Nodes.
   */
  Node substitute(TNode node, TNode replacement) const;

  /**
   * Simultaneous substitution of Nodes.  Elements in the Iterator1
   * range will be replaced by their corresponding element in the
   * Iterator2 range.  Both ranges should have the same size.
   */
  template <class Iterator1, class Iterator2>
  Node substitute(Iterator1 nodesBegin,
                  Iterator1 nodesEnd,
                  Iterator2 replacementsBegin,
                  Iterator2 replacementsEnd) const;

  /**
   * Simultaneous substitution of Nodes.  Iterators should be over
   * pairs (x,y) for the rewrites [x->y].
   */
  template <class Iterator>
  Node substitute(Iterator substitutionsBegin,
                  Iterator substitutionsEnd) const;

  /**
   * Returns the kind of this node.
   * @return the kind
   */
  inline Kind getKind() const {
    assertTNodeNotExpired();
    return Kind(d_nv->d_kind);
  }

  /**
   * Returns the metakind of this node.
   * @return the metakind
   */
  inline kind::MetaKind getMetaKind() const {
    assertTNodeNotExpired();
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
   * Returns the reference count of this node.
   * @return the refcount
   */
  unsigned getRefCount() const {
    return d_nv->getRefCount();
  }

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

  class kinded_iterator {
    friend class NodeTemplate<ref_count>;

    NodeTemplate<ref_count> d_node;
    ssize_t d_child;

    kinded_iterator(TNode node, ssize_t child) :
      d_node(node),
      d_child(child) {
    }

    // These are factories to serve as clients to Node::begin<K>() and
    // Node::end<K>().
    static kinded_iterator begin(TNode n, Kind k) {
      return kinded_iterator(n, n.getKind() == k ? 0 : -2);
    }
    static kinded_iterator end(TNode n, Kind k) {
      return kinded_iterator(n, n.getKind() == k ? n.getNumChildren() : -1);
    }

  public:
    typedef NodeTemplate<ref_count> value_type;
    typedef std::ptrdiff_t difference_type;
    typedef NodeTemplate<ref_count>* pointer;
    typedef NodeTemplate<ref_count>& reference;

    kinded_iterator() :
      d_node(NodeTemplate<ref_count>::null()),
      d_child(-2) {
    }

    kinded_iterator(const kinded_iterator& i) :
      d_node(i.d_node),
      d_child(i.d_child) {
    }

    NodeTemplate<ref_count> operator*() {
      return d_child < 0 ? d_node : d_node[d_child];
    }

    bool operator==(const kinded_iterator& i) {
      return d_node == i.d_node && d_child == i.d_child;
    }

    bool operator!=(const kinded_iterator& i) {
      return !(*this == i);
    }

    kinded_iterator& operator++() {
      if(d_child != -1) {
        ++d_child;
      }
      return *this;
    }

    kinded_iterator operator++(int) {
      kinded_iterator i = *this;
      ++*this;
      return i;
    }
  };/* class NodeTemplate<ref_count>::kinded_iterator */

  typedef kinded_iterator const_kinded_iterator;

  /**
   * Returns the iterator pointing to the first child.
   * @return the iterator
   */
  inline iterator begin() {
    assertTNodeNotExpired();
    return d_nv->begin< NodeTemplate<ref_count> >();
  }

  /**
   * Returns the iterator pointing to the end of the children (one beyond the
   * last one).
   * @return the end of the children iterator.
   */
  inline iterator end() {
    assertTNodeNotExpired();
    return d_nv->end< NodeTemplate<ref_count> >();
  }

  /**
   * Returns the iterator pointing to the first child, if the node's
   * kind is the same as the parameter, otherwise returns the iterator
   * pointing to the node itself.  This is useful if you want to
   * pretend to iterate over a "unary" PLUS, for instance, since unary
   * PLUSes don't exist---begin(PLUS) will give an iterator over the
   * children if the node's a PLUS node, otherwise give an iterator
   * over the node itself, as if it were a unary PLUS.
   * @param kind the kind to match
   * @return the kinded_iterator iterating over this Node (if its kind
   * is not the passed kind) or its children
   */
  inline kinded_iterator begin(Kind kind) {
    assertTNodeNotExpired();
    return kinded_iterator::begin(*this, kind);
  }

  /**
   * Returns the iterator pointing to the end of the children (one
   * beyond the last one), if the node's kind is the same as the
   * parameter, otherwise returns the iterator pointing to the
   * one-of-the-node-itself.  This is useful if you want to pretend to
   * iterate over a "unary" PLUS, for instance, since unary PLUSes
   * don't exist---begin(PLUS) will give an iterator over the children
   * if the node's a PLUS node, otherwise give an iterator over the
   * node itself, as if it were a unary PLUS.
   * @param kind the kind to match
   * @return the kinded_iterator pointing off-the-end of this Node (if
   * its kind is not the passed kind) or off-the-end of its children
   */
  inline kinded_iterator end(Kind kind) {
    assertTNodeNotExpired();
    return kinded_iterator::end(*this, kind);
  }

  /**
   * Returns the const_iterator pointing to the first child.
   * @return the const_iterator
   */
  inline const_iterator begin() const {
    assertTNodeNotExpired();
    return d_nv->begin< NodeTemplate<ref_count> >();
  }

  /**
   * Returns the const_iterator pointing to the end of the children (one
   * beyond the last one.
   * @return the end of the children const_iterator.
   */
  inline const_iterator end() const {
    assertTNodeNotExpired();
    return d_nv->end< NodeTemplate<ref_count> >();
  }

  /**
   * Returns the iterator pointing to the first child, if the node's
   * kind is the same as the parameter, otherwise returns the iterator
   * pointing to the node itself.  This is useful if you want to
   * pretend to iterate over a "unary" PLUS, for instance, since unary
   * PLUSes don't exist---begin(PLUS) will give an iterator over the
   * children if the node's a PLUS node, otherwise give an iterator
   * over the node itself, as if it were a unary PLUS.
   * @param kind the kind to match
   * @return the kinded_iterator iterating over this Node (if its kind
   * is not the passed kind) or its children
   */
  inline const_kinded_iterator begin(Kind kind) const {
    assertTNodeNotExpired();
    return const_kinded_iterator::begin(*this, kind);
  }

  /**
   * Returns the iterator pointing to the end of the children (one
   * beyond the last one), if the node's kind is the same as the
   * parameter, otherwise returns the iterator pointing to the
   * one-of-the-node-itself.  This is useful if you want to pretend to
   * iterate over a "unary" PLUS, for instance, since unary PLUSes
   * don't exist---begin(PLUS) will give an iterator over the children
   * if the node's a PLUS node, otherwise give an iterator over the
   * node itself, as if it were a unary PLUS.
   * @param kind the kind to match
   * @return the kinded_iterator pointing off-the-end of this Node (if
   * its kind is not the passed kind) or off-the-end of its children
   */
  inline const_kinded_iterator end(Kind kind) const {
    assertTNodeNotExpired();
    return const_kinded_iterator::end(*this, kind);
  }

  /**
   * Converts this node into a string representation.
   * @return the string representation of this node.
   */
  inline std::string toString() const {
    assertTNodeNotExpired();
    return d_nv->toString();
  }

  /**
   * Converts this node into a string representation and sends it to the
   * given stream
   *
   * @param out the stream to serialize this node to
   * @param toDepth the depth to which to print this expression, or -1 to
   * print it fully
   * @param types set to true to ascribe types to the output expressions
   * (might break language compliance, but good for debugging expressions)
   * @param language the language in which to output
   */
  inline void toStream(std::ostream& out, int toDepth = -1, bool types = false, size_t dag = 1,
                       OutputLanguage language = language::output::LANG_AUTO) const {
    assertTNodeNotExpired();
    d_nv->toStream(out, toDepth, types, dag, language);
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
   * IOStream manipulator to print expressions as DAGs (or not).
   */
  typedef expr::ExprDag dag;

  /**
   * IOStream manipulator to set the output language for Exprs.
   */
  typedef language::SetLanguage setlanguage;

  /**
   * Very basic pretty printer for Node.
   * @param out output stream to print to.
   * @param indent number of spaces to indent the formula by.
   */
  inline void printAst(std::ostream& out, int indent = 0) const;

  /**
   * Check if the node has a subterm t.
   */
  inline bool hasSubterm(NodeTemplate<false> t, bool strict = false) const;

  template <bool ref_count2>
  NodeTemplate<true> eqNode(const NodeTemplate<ref_count2>& right) const;

  NodeTemplate<true> notNode() const;
  NodeTemplate<true> negate() const;
  template <bool ref_count2>
  NodeTemplate<true> andNode(const NodeTemplate<ref_count2>& right) const;
  template <bool ref_count2>
  NodeTemplate<true> orNode(const NodeTemplate<ref_count2>& right) const;
  template <bool ref_count2, bool ref_count3>
  NodeTemplate<true> iteNode(const NodeTemplate<ref_count2>& thenpart,
                             const NodeTemplate<ref_count3>& elsepart) const;
  template <bool ref_count2>
  NodeTemplate<true> impNode(const NodeTemplate<ref_count2>& right) const;
  template <bool ref_count2>
  NodeTemplate<true> xorNode(const NodeTemplate<ref_count2>& right) const;

};/* class NodeTemplate<ref_count> */

/**
 * Serializes a given node to the given stream.
 *
 * @param out the output stream to use
 * @param n the node to output to the stream
 * @return the stream
 */
inline std::ostream& operator<<(std::ostream& out, TNode n) {
  n.toStream(out,
             Node::setdepth::getDepth(out),
             Node::printtypes::getPrintTypes(out),
             Node::dag::getDag(out),
             Node::setlanguage::getLanguage(out));
  return out;
}

namespace {

template <typename T>
void nodeContainerToOut(std::ostream& out, const T& container)
{
  out << "[";
  bool is_first = true;
  for (const auto& item : container)
  {
    out << (!is_first ? ", " : "") << item;
    is_first = false;
  }
  out << "]";
}

}

/**
 * Serialize a vector of nodes to given stream.
 *
 * @param out the output stream to use
 * @param container the vector of nodes to output to the stream
 * @return the stream
 */
template <bool RC>
std::ostream& operator<<(std::ostream& out,
                         const std::vector<NodeTemplate<RC>>& container)
{
  nodeContainerToOut(out, container);
  return out;
}

/**
 * Serialize a set of nodes to the given stream.
 *
 * @param out the output stream to use
 * @param container the set of nodes to output to the stream
 * @return the stream
 */
template <bool RC>
std::ostream& operator<<(std::ostream& out,
                         const std::set<NodeTemplate<RC>>& container)
{
  nodeContainerToOut(out, container);
  return out;
}

/**
 * Serialize an unordered_set of nodes to the given stream.
 *
 * @param out the output stream to use
 * @param container the unordered_set of nodes to output to the stream
 * @return the stream
 */
template <bool RC, typename hash_function>
std::ostream& operator<<(
    std::ostream& out,
    const std::unordered_set<NodeTemplate<RC>, hash_function>& container)
{
  nodeContainerToOut(out, container);
  return out;
}

/**
 * Serialize a map of nodes to the given stream.
 *
 * @param out the output stream to use
 * @param container the map of nodes to output to the stream
 * @return the stream
 */
template <bool RC, typename V>
std::ostream& operator<<(
    std::ostream& out,
    const std::map<NodeTemplate<RC>, V>& container)
{
  nodeContainerToOut(out, container);
  return out;
}

/**
 * Serialize an unordered_map of nodes to the given stream.
 *
 * @param out the output stream to use
 * @param container the unordered_map of nodes to output to the stream
 * @return the stream
 */
template <bool RC, typename V, typename HF>
std::ostream& operator<<(
    std::ostream& out,
    const std::unordered_map<NodeTemplate<RC>, V, HF>& container)
{
  nodeContainerToOut(out, container);
  return out;
}

}/* CVC4 namespace */

//#include "expr/attribute.h"
#include "expr/node_manager.h"
#include "expr/type_checker.h"

namespace CVC4 {

inline size_t NodeHashFunction::operator()(Node node) const {
  return node.getId();
}
inline size_t TNodeHashFunction::operator()(TNode node) const {
  return node.getId();
}

using TNodePairHashFunction =
    PairHashFunction<TNode, TNode, TNodeHashFunction, TNodeHashFunction>;

template <bool ref_count>
inline size_t NodeTemplate<ref_count>::getNumChildren() const {
  assertTNodeNotExpired();
  return d_nv->getNumChildren();
}

template <bool ref_count>
template <class T>
inline const T& NodeTemplate<ref_count>::getConst() const {
  assertTNodeNotExpired();
  return d_nv->getConst<T>();
}

template <bool ref_count>
template <class AttrKind>
inline typename AttrKind::value_type NodeTemplate<ref_count>::
getAttribute(const AttrKind&) const {
  Assert( NodeManager::currentNM() != NULL,
          "There is no current CVC4::NodeManager associated to this thread.\n"
          "Perhaps a public-facing function is missing a NodeManagerScope ?" );

  assertTNodeNotExpired();

  return NodeManager::currentNM()->getAttribute(*this, AttrKind());
}

template <bool ref_count>
template <class AttrKind>
inline bool NodeTemplate<ref_count>::
hasAttribute(const AttrKind&) const {
  Assert( NodeManager::currentNM() != NULL,
          "There is no current CVC4::NodeManager associated to this thread.\n"
          "Perhaps a public-facing function is missing a NodeManagerScope ?" );

  assertTNodeNotExpired();

  return NodeManager::currentNM()->hasAttribute(*this, AttrKind());
}

template <bool ref_count>
template <class AttrKind>
inline bool NodeTemplate<ref_count>::getAttribute(const AttrKind&,
                                                  typename AttrKind::value_type& ret) const {
  Assert( NodeManager::currentNM() != NULL,
          "There is no current CVC4::NodeManager associated to this thread.\n"
          "Perhaps a public-facing function is missing a NodeManagerScope ?" );

  assertTNodeNotExpired();

  return NodeManager::currentNM()->getAttribute(*this, AttrKind(), ret);
}

template <bool ref_count>
template <class AttrKind>
inline void NodeTemplate<ref_count>::
setAttribute(const AttrKind&, const typename AttrKind::value_type& value) {
  Assert( NodeManager::currentNM() != NULL,
          "There is no current CVC4::NodeManager associated to this thread.\n"
          "Perhaps a public-facing function is missing a NodeManagerScope ?" );

  assertTNodeNotExpired();

  NodeManager::currentNM()->setAttribute(*this, AttrKind(), value);
}

template <bool ref_count>
NodeTemplate<ref_count> NodeTemplate<ref_count>::s_null(&expr::NodeValue::null());

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
    Assert(d_nv->d_rc > 0 || d_nv == &expr::NodeValue::null(),
           "TNode constructed from NodeValue with rc == 0");
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
    Assert(d_nv->d_rc > 0, "Node constructed from TNode with rc == 0");
    d_nv->inc();
  } else {
    // shouldn't ever fail
    Assert(d_nv->d_rc > 0, "TNode constructed from Node with rc == 0");
  }
}

template <bool ref_count>
NodeTemplate<ref_count>::NodeTemplate(const NodeTemplate& e) {
  Assert(e.d_nv != NULL, "Expecting a non-NULL expression value!");
  d_nv = e.d_nv;
  if(ref_count) {
    // shouldn't ever fail
    Assert(d_nv->d_rc > 0, "Node constructed from Node with rc == 0");
    d_nv->inc();
  } else {
    Assert(d_nv->d_rc > 0, "TNode constructed from TNode with rc == 0");
  }
}

template <bool ref_count>
NodeTemplate<ref_count>::NodeTemplate(const Expr& e) {
  Assert(e.d_node != NULL, "Expecting a non-NULL expression value!");
  Assert(e.d_node->d_nv != NULL, "Expecting a non-NULL expression value!");
  d_nv = e.d_node->d_nv;
  // shouldn't ever fail
  Assert(d_nv->d_rc > 0, "Node constructed from Expr with rc == 0");
  if(ref_count) {
    d_nv->inc();
  }
}

template <bool ref_count>
NodeTemplate<ref_count>::~NodeTemplate() {
  Assert(d_nv != NULL, "Expecting a non-NULL expression value!");
  if(ref_count) {
    // shouldn't ever fail
    Assert(d_nv->d_rc > 0, "Node reference count would be negative");
    d_nv->dec();
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
  if(__builtin_expect( ( d_nv != e.d_nv ), true )) {
    if(ref_count) {
      // shouldn't ever fail
      Assert(d_nv->d_rc > 0,
             "Node reference count would be negative");
      d_nv->dec();
    }
    d_nv = e.d_nv;
    if(ref_count) {
      // shouldn't ever fail
      Assert(d_nv->d_rc > 0, "Node assigned from Node with rc == 0");
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
  if(__builtin_expect( ( d_nv != e.d_nv ), true )) {
    if(ref_count) {
      // shouldn't ever fail
      Assert(d_nv->d_rc > 0, "Node reference count would be negative");
      d_nv->dec();
    }
    d_nv = e.d_nv;
    if(ref_count) {
      Assert(d_nv->d_rc > 0, "Node assigned from TNode with rc == 0");
      d_nv->inc();
    } else {
      // shouldn't ever happen
      Assert(d_nv->d_rc > 0, "TNode assigned from Node with rc == 0");
    }
  }
  return *this;
}

template <bool ref_count>
template <bool ref_count2>
NodeTemplate<true>
NodeTemplate<ref_count>::eqNode(const NodeTemplate<ref_count2>& right) const {
  assertTNodeNotExpired();
  return NodeManager::currentNM()->mkNode(kind::EQUAL, *this, right);
}

template <bool ref_count>
NodeTemplate<true> NodeTemplate<ref_count>::notNode() const {
  assertTNodeNotExpired();
  return NodeManager::currentNM()->mkNode(kind::NOT, *this);
}

template <bool ref_count>
NodeTemplate<true> NodeTemplate<ref_count>::negate() const {
  assertTNodeNotExpired();
  return (getKind() == kind::NOT) ? NodeTemplate<true>(d_nv->getChild(0)) : NodeManager::currentNM()->mkNode(kind::NOT, *this);
}

template <bool ref_count>
template <bool ref_count2>
NodeTemplate<true>
NodeTemplate<ref_count>::andNode(const NodeTemplate<ref_count2>& right) const {
  assertTNodeNotExpired();
  return NodeManager::currentNM()->mkNode(kind::AND, *this, right);
}

template <bool ref_count>
template <bool ref_count2>
NodeTemplate<true>
NodeTemplate<ref_count>::orNode(const NodeTemplate<ref_count2>& right) const {
  assertTNodeNotExpired();
  return NodeManager::currentNM()->mkNode(kind::OR, *this, right);
}

template <bool ref_count>
template <bool ref_count2, bool ref_count3>
NodeTemplate<true>
NodeTemplate<ref_count>::iteNode(const NodeTemplate<ref_count2>& thenpart,
                                 const NodeTemplate<ref_count3>& elsepart) const {
  assertTNodeNotExpired();
  return NodeManager::currentNM()->mkNode(kind::ITE, *this, thenpart, elsepart);
}

template <bool ref_count>
template <bool ref_count2>
NodeTemplate<true>
NodeTemplate<ref_count>::impNode(const NodeTemplate<ref_count2>& right) const {
  assertTNodeNotExpired();
  return NodeManager::currentNM()->mkNode(kind::IMPLIES, *this, right);
}

template <bool ref_count>
template <bool ref_count2>
NodeTemplate<true>
NodeTemplate<ref_count>::xorNode(const NodeTemplate<ref_count2>& right) const {
  assertTNodeNotExpired();
  return NodeManager::currentNM()->mkNode(kind::XOR, *this, right);
}

template <bool ref_count>
inline void
NodeTemplate<ref_count>::printAst(std::ostream& out, int indent) const {
  assertTNodeNotExpired();
  d_nv->printAst(out, indent);
}

/**
 * Returns a node representing the operator of this expression.
 * If this is an APPLY, then the operator will be a functional term.
 * Otherwise, it will be a node with kind BUILTIN.
 */
template <bool ref_count>
NodeTemplate<true> NodeTemplate<ref_count>::getOperator() const {
  Assert( NodeManager::currentNM() != NULL,
          "There is no current CVC4::NodeManager associated to this thread.\n"
          "Perhaps a public-facing function is missing a NodeManagerScope ?" );

  assertTNodeNotExpired();

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

  case kind::metakind::NULLARY_OPERATOR:
    IllegalArgument(*this, "getOperator() called on Node with NULLARY_OPERATOR-kinded kind");

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
  assertTNodeNotExpired();
  return NodeManager::hasOperator(getKind());
}

template <bool ref_count>
TypeNode NodeTemplate<ref_count>::getType(bool check) const
{
  Assert( NodeManager::currentNM() != NULL,
          "There is no current CVC4::NodeManager associated to this thread.\n"
          "Perhaps a public-facing function is missing a NodeManagerScope ?" );

  assertTNodeNotExpired();

  return NodeManager::currentNM()->getType(*this, check);
}

template <bool ref_count>
inline Node
NodeTemplate<ref_count>::substitute(TNode node, TNode replacement) const {
  if (node == *this) {
    return replacement;
  }
  std::unordered_map<TNode, TNode, TNodeHashFunction> cache;
  return substitute(node, replacement, cache);
}

template <bool ref_count>
Node
NodeTemplate<ref_count>::substitute(TNode node, TNode replacement,
                                    std::unordered_map<TNode, TNode, TNodeHashFunction>& cache) const {
  Assert(node != *this);

  if (getNumChildren() == 0) {
    return *this;
  }

  // in cache?
  typename std::unordered_map<TNode, TNode, TNodeHashFunction>::const_iterator i = cache.find(*this);
  if(i != cache.end()) {
    return (*i).second;
  }

  // otherwise compute
  NodeBuilder<> nb(getKind());
  if(getMetaKind() == kind::metakind::PARAMETERIZED) {
    // push the operator
    if(getOperator() == node) {
      nb << replacement;
    } else {
      nb << getOperator().substitute(node, replacement, cache);
    }
  }
  for(const_iterator i = begin(),
        iend = end();
      i != iend;
      ++i) {
    if(*i == node) {
      nb << replacement;
    } else {
      nb << (*i).substitute(node, replacement, cache);
    }
  }

  // put in cache
  Node n = nb;
  Assert(node != n);
  cache[*this] = n;
  return n;
}

template <bool ref_count>
template <class Iterator1, class Iterator2>
inline Node
NodeTemplate<ref_count>::substitute(Iterator1 nodesBegin,
                                    Iterator1 nodesEnd,
                                    Iterator2 replacementsBegin,
                                    Iterator2 replacementsEnd) const {
  std::unordered_map<TNode, TNode, TNodeHashFunction> cache;
  return substitute(nodesBegin, nodesEnd,
                    replacementsBegin, replacementsEnd, cache);
}

template <bool ref_count>
template <class Iterator1, class Iterator2>
Node
NodeTemplate<ref_count>::substitute(Iterator1 nodesBegin,
                                    Iterator1 nodesEnd,
                                    Iterator2 replacementsBegin,
                                    Iterator2 replacementsEnd,
                                    std::unordered_map<TNode, TNode, TNodeHashFunction>& cache) const {
  // in cache?
  typename std::unordered_map<TNode, TNode, TNodeHashFunction>::const_iterator i = cache.find(*this);
  if(i != cache.end()) {
    return (*i).second;
  }

  // otherwise compute
  Assert( std::distance(nodesBegin, nodesEnd) == std::distance(replacementsBegin, replacementsEnd),
          "Substitution iterator ranges must be equal size" );
  Iterator1 j = find(nodesBegin, nodesEnd, TNode(*this));
  if(j != nodesEnd) {
    Iterator2 b = replacementsBegin;
    std::advance(b, std::distance(nodesBegin, j));
    Node n = *b;
    cache[*this] = n;
    return n;
  } else if(getNumChildren() == 0) {
    cache[*this] = *this;
    return *this;
  } else {
    NodeBuilder<> nb(getKind());
    if(getMetaKind() == kind::metakind::PARAMETERIZED) {
      // push the operator
      nb << getOperator().substitute(nodesBegin, nodesEnd,
                                     replacementsBegin, replacementsEnd,
                                     cache);
    }
    for(const_iterator i = begin(),
          iend = end();
        i != iend;
        ++i) {
      nb << (*i).substitute(nodesBegin, nodesEnd,
                            replacementsBegin, replacementsEnd,
                            cache);
    }
    Node n = nb;
    cache[*this] = n;
    return n;
  }
}

template <bool ref_count>
template <class Iterator>
inline Node
NodeTemplate<ref_count>::substitute(Iterator substitutionsBegin,
                                    Iterator substitutionsEnd) const {
  std::unordered_map<TNode, TNode, TNodeHashFunction> cache;
  return substitute(substitutionsBegin, substitutionsEnd, cache);
}

template <bool ref_count>
template <class Iterator>
Node
NodeTemplate<ref_count>::substitute(Iterator substitutionsBegin,
                                    Iterator substitutionsEnd,
                                    std::unordered_map<TNode, TNode, TNodeHashFunction>& cache) const {
  // in cache?
  typename std::unordered_map<TNode, TNode, TNodeHashFunction>::const_iterator i = cache.find(*this);
  if(i != cache.end()) {
    return (*i).second;
  }

  // otherwise compute
  Iterator j = find_if(substitutionsBegin, substitutionsEnd,
                       bind2nd(first_equal_to<typename Iterator::value_type::first_type, typename Iterator::value_type::second_type>(), *this));
  if(j != substitutionsEnd) {
    Node n = (*j).second;
    cache[*this] = n;
    return n;
  } else if(getNumChildren() == 0) {
    cache[*this] = *this;
    return *this;
  } else {
    NodeBuilder<> nb(getKind());
    if(getMetaKind() == kind::metakind::PARAMETERIZED) {
      // push the operator
      nb << getOperator().substitute(substitutionsBegin, substitutionsEnd, cache);
    }
    for(const_iterator i = begin(),
          iend = end();
        i != iend;
        ++i) {
      nb << (*i).substitute(substitutionsBegin, substitutionsEnd, cache);
    }
    Node n = nb;
    cache[*this] = n;
    return n;
  }
}

template <bool ref_count>
inline Expr NodeTemplate<ref_count>::toExpr() const {
  assertTNodeNotExpired();
  return NodeManager::currentNM()->toExpr(*this);
}

// intentionally not defined for TNode
template <>
inline Node NodeTemplate<true>::fromExpr(const Expr& e) {
  return NodeManager::fromExpr(e);
}

template<bool ref_count>
bool NodeTemplate<ref_count>::hasSubterm(NodeTemplate<false> t, bool strict) const {
  typedef std::unordered_set<TNode, TNodeHashFunction> node_set;

  if (!strict && *this == t) {
    return true;
  }

  node_set visited;
  std::vector<TNode> toProcess;

  toProcess.push_back(*this);

  for (unsigned i = 0; i < toProcess.size(); ++ i) {
    TNode current = toProcess[i];
    for(unsigned j = 0, j_end = current.getNumChildren(); j < j_end; ++ j) {
      TNode child = current[j];
      if (child == t) {
        return true;
      }
      if (visited.find(child) != visited.end()) {
        continue;
      } else {
        visited.insert(child);
        toProcess.push_back(child);
      }
    }
  }

  return false;
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
  Warning() << Node::setdepth(-1)
            << Node::printtypes(false)
            << Node::dag(true)
            << Node::setlanguage(language::output::LANG_AST)
            << n << std::endl;
  Warning().flush();
}
static void __attribute__((used)) debugPrintNodeNoDag(const NodeTemplate<true>& n) {
  Warning() << Node::setdepth(-1)
            << Node::printtypes(false)
            << Node::dag(false)
            << Node::setlanguage(language::output::LANG_AST)
            << n << std::endl;
  Warning().flush();
}
static void __attribute__((used)) debugPrintRawNode(const NodeTemplate<true>& n) {
  n.printAst(Warning(), 0);
  Warning().flush();
}

static void __attribute__((used)) debugPrintTNode(const NodeTemplate<false>& n) {
  Warning() << Node::setdepth(-1)
            << Node::printtypes(false)
            << Node::dag(true)
            << Node::setlanguage(language::output::LANG_AST)
            << n << std::endl;
  Warning().flush();
}
static void __attribute__((used)) debugPrintTNodeNoDag(const NodeTemplate<false>& n) {
  Warning() << Node::setdepth(-1)
            << Node::printtypes(false)
            << Node::dag(false)
            << Node::setlanguage(language::output::LANG_AST)
            << n << std::endl;
  Warning().flush();
}
static void __attribute__((used)) debugPrintRawTNode(const NodeTemplate<false>& n) {
  n.printAst(Warning(), 0);
  Warning().flush();
}
#endif /* CVC4_DEBUG */

}/* CVC4 namespace */

#endif /* __CVC4__NODE_H */
