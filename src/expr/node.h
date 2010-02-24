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

class Type;
class NodeManager;
template<bool ref_count>
  class NodeTemplate;

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
}/* CVC4::expr namespace */

using CVC4::expr::NodeValue;

/**
 * Encapsulation of an NodeValue pointer.  The reference count is
 * maintained in the NodeValue if ref_count is true.
 * @param ref_count if true reference are counted in the NodeValue
 */
template<bool ref_count>
  class NodeTemplate {

    /**
     * The NodeValue has access to the private constructors, so that the iterators
     * can can create new nodes.
     */
    friend class NodeValue;

    /** A convenient null-valued encapsulated pointer */
    static NodeTemplate s_null;

    /** The referenced NodeValue */
    NodeValue* d_nv;

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
    explicit NodeTemplate(const NodeValue*);

    friend class NodeTemplate<true> ;
    friend class NodeTemplate<false> ;
    friend class NodeManager;
    template<unsigned>
      friend class NodeBuilder;

    /**
     * Assigns the expression value and does reference counting. No assumptions
     * are made on the expression, and should only be used if we know what we are
     * doing.
     *
     * @param ev the expression value to assign
     */
    void assignNodeValue(NodeValue* ev);

  public:

    /** Default constructor, makes a null expression. */
    NodeTemplate() : d_nv(&NodeValue::s_null) { }

    /**
     * Copy constructor for nodes that can accept the nodes that are reference
     * counted or not.
     * @param node the node to make copy of
     */
    template<bool ref_count_1>
      NodeTemplate(const NodeTemplate<ref_count_1>& node);

    /**
     * Assignment operator for nodes, copies the relevant information from node
     * to this node.
     * @param node the node to copy
     * @return reference to this node
     */
    template<bool ref_count_1>
      NodeTemplate& operator=(const NodeTemplate<ref_count_1>& node);

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
      return d_nv == &NodeValue::s_null;
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
      Assert(i >= 0 && unsigned(i) < d_nv->d_nchildren);
      return NodeTemplate(d_nv->d_children[i]);
    }

    /**
     * Returns true if this node is atomic (has no more Boolean structure)
     * @return true if atomic
     */
    bool isAtomic() const;

    /**
     * Returns the hash value of this node.
     * @return the hash value
     */
    size_t hash() const {
      return d_nv->getId();
    }

    /**
     * Returns the unique id of this node
     * @return the ud
     */
    uint64_t getId() const {
      return d_nv->getId();
    }

    /**
     * Returns the type of this node.
     * @return the type
     */
    const Type* getType() const;

    /**
     * Returns the kind of this node.
     * @return the kind
     */
    inline Kind getKind() const {
      return Kind(d_nv->d_kind);
    }

    /**
     * Returns the number of children this node has.
     * @return the number of children
     */
    inline size_t getNumChildren() const;

    /**
     * Returns the value of the given attribute that this has been attached.
     * @param attKind the kind of the attribute
     * @return the value of the attribute
     */
    template<class AttrKind>
      inline typename AttrKind::value_type getAttribute(const AttrKind& attKind) const;

    /**
     * Returns true if this node has been associated an attribute of given kind.
     * Additionaly, if a pointer to the value_kind is give, and the attribute
     * value has been set for this node, it will be returned.
     * @param attKind the kind of the attribute
     * @param value where to store the value if it exists
     * @return true if this node has the requested attribute
     */
    template<class AttrKind>
      inline bool hasAttribute(const AttrKind& attKind, typename AttrKind::value_type* value = NULL) const;

    /** Iterator allowing for scanning through the children. */
    typedef typename NodeValue::iterator<ref_count> iterator;
    /** Constant iterator allowing for scanning through the children. */
    typedef typename NodeValue::iterator<ref_count> const_iterator;

    /**
     * Returns the iterator pointing to the first child.
     * @return the iterator
     */
    inline iterator begin() {
      return d_nv->begin<ref_count>();
    }

    /**
     * Returns the iterator pointing to the end of the children (one beyond the
     * last one.
     * @return the end of the children iterator.
     */
    inline iterator end() {
      return d_nv->end<ref_count>();
    }

    /**
     * Returns the const_iterator pointing to the first child.
     * @return the const_iterator
     */
    inline const_iterator begin() const {
      return d_nv->begin<ref_count>();
    }

    /**
     * Returns the const_iterator pointing to the end of the children (one
     * beyond the last one.
     * @return the end of the children const_iterator.
     */
    inline const_iterator end() const {
      return d_nv->end<ref_count>();
    }

    /**
     * Converts this node into a string representation.
     * @return the string representation of this node.
     */
    inline std::string toString() const {
      return d_nv->toString();
    }

    /**
     * Converst this node into a string representation and sends it to the
     * given stream
     * @param out the sream to serialise this node to
     */
    inline void toStream(std::ostream& out) const {
      d_nv->toStream(out);
    }

    /**
     * Very basic pretty printer for Node.
     * @param o output stream to print to.
     * @param indent number of spaces to indent the formula by.
     */
    void printAst(std::ostream & o, int indent = 0) const;

    NodeTemplate eqNode(const NodeTemplate& right) const;

    NodeTemplate notNode() const;
    NodeTemplate andNode(const NodeTemplate& right) const;
    NodeTemplate orNode(const NodeTemplate& right) const;
    NodeTemplate iteNode(const NodeTemplate& thenpart,
                         const NodeTemplate& elsepart) const;
    NodeTemplate iffNode(const NodeTemplate& right) const;
    NodeTemplate impNode(const NodeTemplate& right) const;
    NodeTemplate xorNode(const NodeTemplate& right) const;

    NodeTemplate plusNode(const NodeTemplate& right) const;
    NodeTemplate uMinusNode() const;
    NodeTemplate multNode(const NodeTemplate& right) const;

    /**
     * Sets the given attribute of this node to the given value.
     * @param attKind the kind of the atribute
     * @param value the value to set the attribute to
     */
    template<class AttrKind>
      inline void setAttribute(const AttrKind& attKind,
                               const typename AttrKind::value_type& value);

  private:

    /**
     * Pretty printer for use within gdb.  This is not intended to be used
     * outside of gdb.  This writes to the Warning() stream and immediately
     * flushes the stream.
     */
    void debugPrint();


    /**
     * Indents the given stream a given amount of spaces.
     * @param out the stream to indent
     * @param indent the numer of spaces
     */
    static void indent(std::ostream& out, int indent) {
      for(int i = 0; i < indent; i++)
        out << ' ';
    }

  };/* class NodeTemplate */

/**
 * Serializes a given node to the given stream.
 * @param out the output stream to use
 * @param node the node to output to the stream
 * @return the changed stream.
 */
inline std::ostream& operator<<(std::ostream& out, const Node& node) {
  node.toStream(out);
  return out;
}

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
  inline size_t NodeTemplate<ref_count>::getNumChildren() const {
    return d_nv->d_nchildren;
  }

template<bool ref_count>
  template<class AttrKind>
    inline typename AttrKind::value_type NodeTemplate<ref_count>::
    getAttribute(const AttrKind&) const {
      Assert( NodeManager::currentNM() != NULL,
          "There is no current CVC4::NodeManager associated to this thread.\n"
          "Perhaps a public-facing function is missing a NodeManagerScope ?" );
      return NodeManager::currentNM()->getAttribute(*this, AttrKind());
    }

template<bool ref_count>
  template<class AttrKind>
    inline bool NodeTemplate<ref_count>::
    hasAttribute(const AttrKind&, typename AttrKind::value_type* ret) const {
      Assert( NodeManager::currentNM() != NULL,
          "There is no current CVC4::NodeManager associated to this thread.\n"
          "Perhaps a public-facing function is missing a NodeManagerScope ?" );
      return NodeManager::currentNM()->hasAttribute(*this, AttrKind(), ret);
    }

template<bool ref_count>
  template<class AttrKind>
    inline void NodeTemplate<ref_count>::
    setAttribute(const AttrKind&, const typename AttrKind::value_type& value) {
      Assert( NodeManager::currentNM() != NULL,
          "There is no current CVC4::NodeManager associated to this thread.\n"
          "Perhaps a public-facing function is missing a NodeManagerScope ?" );
      NodeManager::currentNM()->setAttribute(*this, AttrKind(), value);
    }

template<bool ref_count>
  NodeTemplate<ref_count> NodeTemplate<ref_count>::s_null(&NodeValue::s_null);

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

// FIXME: escape from type system convenient but is there a better
// way?  Nodes conceptually don't change their expr values but of
// course they do modify the refcount.  But it's nice to be able to
// support node_iterators over const NodeValue*.  So.... hm.
template<bool ref_count>
  NodeTemplate<ref_count>::NodeTemplate(const NodeValue* ev) :
    d_nv(const_cast<NodeValue*> (ev)) {
    Assert(d_nv != NULL, "Expecting a non-NULL expression value!");
    if(ref_count)
      d_nv->inc();
  }

template<bool ref_count>
  template<bool ref_count_1>
    NodeTemplate<ref_count>::NodeTemplate(const NodeTemplate<ref_count_1>& e) {
      Assert(e.d_nv != NULL, "Expecting a non-NULL expression value!");
      d_nv = e.d_nv;
      if(ref_count)
        d_nv->inc();
    }

template<bool ref_count>
  NodeTemplate<ref_count>::~NodeTemplate() {
    Assert(d_nv != NULL, "Expecting a non-NULL expression value!");
    if(ref_count)
      d_nv->dec();
    Assert(ref_count || d_nv->d_rc > 0,
        "Temporary node pointing to an expired node");
  }

template<bool ref_count>
  void NodeTemplate<ref_count>::assignNodeValue(NodeValue* ev) {
    d_nv = ev;
    if(ref_count)
      d_nv->inc();
  }

template<bool ref_count>
  template<bool ref_count_1>
    NodeTemplate<ref_count>& NodeTemplate<ref_count>::
    operator=(const NodeTemplate<ref_count_1>& e) {
      Assert(d_nv != NULL, "Expecting a non-NULL expression value!");
      Assert(e.d_nv != NULL, "Expecting a non-NULL expression value on RHS!");
      if(EXPECT_TRUE( d_nv != e.d_nv )) {
        if(ref_count)
          d_nv->dec();
        d_nv = e.d_nv;
        if(ref_count)
          d_nv->inc();
      }
      return *this;
    }

template<bool ref_count>
  NodeTemplate<ref_count> NodeTemplate<ref_count>::eqNode(const NodeTemplate<
      ref_count>& right) const {
    return NodeManager::currentNM()->mkNode(EQUAL, *this, right);
  }

template<bool ref_count>
  NodeTemplate<ref_count> NodeTemplate<ref_count>::notNode() const {
    return NodeManager::currentNM()->mkNode(NOT, *this);
  }

template<bool ref_count>
  NodeTemplate<ref_count> NodeTemplate<ref_count>::andNode(const NodeTemplate<
      ref_count>& right) const {
    return NodeManager::currentNM()->mkNode(AND, *this, right);
  }

template<bool ref_count>
  NodeTemplate<ref_count> NodeTemplate<ref_count>::orNode(const NodeTemplate<
      ref_count>& right) const {
    return NodeManager::currentNM()->mkNode(OR, *this, right);
  }

template<bool ref_count>
  NodeTemplate<ref_count> NodeTemplate<ref_count>::iteNode(const NodeTemplate<
      ref_count>& thenpart, const NodeTemplate<ref_count>& elsepart) const {
    return NodeManager::currentNM()->mkNode(ITE, *this, thenpart, elsepart);
  }

template<bool ref_count>
  NodeTemplate<ref_count> NodeTemplate<ref_count>::iffNode(const NodeTemplate<
      ref_count>& right) const {
    return NodeManager::currentNM()->mkNode(IFF, *this, right);
  }

template<bool ref_count>
  NodeTemplate<ref_count> NodeTemplate<ref_count>::impNode(const NodeTemplate<
      ref_count>& right) const {
    return NodeManager::currentNM()->mkNode(IMPLIES, *this, right);
  }

template<bool ref_count>
  NodeTemplate<ref_count> NodeTemplate<ref_count>::xorNode(const NodeTemplate<
      ref_count>& right) const {
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
