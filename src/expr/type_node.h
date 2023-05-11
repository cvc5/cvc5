/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Dejan Jovanovic, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Reference-counted encapsulation of a pointer to node information.
 */

#include "cvc5_private.h"

#include "expr/node.h"

#ifndef CVC5__TYPE_NODE_H
#define CVC5__TYPE_NODE_H

#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>

#include "base/check.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/node_value.h"
#include "util/cardinality_class.h"

namespace cvc5::internal {

class NodeManager;
class Cardinality;
class DType;
class Integer;

namespace expr {
  class NodeValue;
  }  // namespace expr

/**
 * Encapsulation of an NodeValue pointer for Types. The reference count is
 * maintained in the NodeValue.
 */
class CVC5_EXPORT TypeNode
{
 private:

  /**
   * The NodeValue has access to the private constructors, so that the
   * iterators can can create new types.
   */
  friend class expr::NodeValue;

  /** A convenient null-valued encapsulated pointer */
  static TypeNode s_null;

  /** The referenced NodeValue */
  expr::NodeValue* d_nv;

  /**
   * This constructor is reserved for use by the TypeNode package.
   */
  explicit TypeNode(const expr::NodeValue*);

  friend class NodeManager;

  friend class NodeBuilder;

  /**
   * Assigns the expression value and does reference counting. No
   * assumptions are made on the expression, and should only be used
   * if we know what we are doing.
   *
   * @param ev the expression value to assign
   */
  void assignNodeValue(expr::NodeValue* ev);

  /**
   * Cache-aware, recursive version of substitute() used by the public
   * member function with a similar signature.
   */
  TypeNode substitute(const TypeNode& type,
                      const TypeNode& replacement,
                      std::unordered_map<TypeNode, TypeNode>& cache) const;

  /**
   * Cache-aware, recursive version of substitute() used by the public
   * member function with a similar signature.
   */
  template <class Iterator1, class Iterator2>
  TypeNode substitute(Iterator1 typesBegin,
                      Iterator1 typesEnd,
                      Iterator2 replacementsBegin,
                      Iterator2 replacementsEnd,
                      std::unordered_map<TypeNode, TypeNode>& cache) const;

 public:
  /** Default constructor, makes a null expression. */
  TypeNode() : d_nv(&expr::NodeValue::null()) { }

  /** Copy constructor */
  TypeNode(const TypeNode& node);

  /**
   * Destructor. If ref_count is true it will decrement the reference count
   * and, if zero, collect the NodeValue.
   */
  ~TypeNode();

  /**
   * Assignment operator for nodes, copies the relevant information from node
   * to this node.
   *
   * @param typeNode the node to copy
   * @return reference to this node
   */
  TypeNode& operator=(const TypeNode& typeNode);

  /**
   * Return the null node.
   *
   * @return the null node
   */
  static TypeNode null() {
    return s_null;
  }

  /**
   * Substitution of TypeNodes.
   */
  inline TypeNode
  substitute(const TypeNode& type, const TypeNode& replacement) const;

  /**
   * Simultaneous substitution of TypeNodes.
   */
  template <class Iterator1, class Iterator2>
  inline TypeNode
  substitute(Iterator1 typesBegin, Iterator1 typesEnd,
             Iterator2 replacementsBegin, Iterator2 replacementsEnd) const;

  /**
   * Structural comparison operator for expressions.
   *
   * @param typeNode the type node to compare to
   * @return true if expressions are equal, false otherwise
   */
  bool operator==(const TypeNode& typeNode) const {
    return d_nv == typeNode.d_nv;
  }

  /**
   * Structural comparison operator for expressions.
   *
   * @param typeNode the type node to compare to
   * @return true if expressions are equal, false otherwise
   */
  bool operator!=(const TypeNode& typeNode) const {
    return !(*this == typeNode);
  }

  /**
   * We compare by expression ids so, keeping things deterministic and having
   * that subexpressions have to be smaller than the enclosing expressions.
   *
   * @param typeNode the node to compare to
   * @return true if this expression is lesser
   */
  inline bool operator<(const TypeNode& typeNode) const {
    return d_nv->d_id < typeNode.d_nv->d_id;
  }

  /**
   * We compare by expression ids so, keeping things deterministic and having
   * that subexpressions have to be smaller than the enclosing expressions.
   *
   * @param typeNode the node to compare to
   * @return true if this expression is lesser or equal
   */
  inline bool operator<=(const TypeNode& typeNode) const {
    return d_nv->d_id <= typeNode.d_nv->d_id;
  }

  /**
   * We compare by expression ids so, keeping things deterministic and having
   * that subexpressions have to be smaller than the enclosing expressions.
   *
   * @param typeNode the node to compare to
   * @return true if this expression is greater
   */
  inline bool operator>(const TypeNode& typeNode) const {
    return d_nv->d_id > typeNode.d_nv->d_id;
  }

  /**
   * We compare by expression ids so, keeping things deterministic and having
   * that subexpressions have to be smaller than the enclosing expressions.
   *
   * @param typeNode the node to compare to
   * @return true if this expression is greater or equal
   */
  inline bool operator>=(const TypeNode& typeNode) const {
    return d_nv->d_id >= typeNode.d_nv->d_id;
  }

  /**
   * Returns the i-th child of this node.
   *
   * @param i the index of the child
   * @return the node representing the i-th child
   */
  inline TypeNode operator[](int i) const {
    return TypeNode(d_nv->getChild(i));
  }

  /**
   * Returns the unique id of this node
   *
   * @return the id
   */
  inline unsigned long getId() const {
    return d_nv->getId();
  }

  /**
   * Returns the kind of this type node.
   *
   * @return the kind
   */
  inline Kind getKind() const {
    return Kind(d_nv->d_kind);
  }

  /**
   * Returns the metakind of this type node.
   *
   * @return the metakind
   */
  inline kind::MetaKind getMetaKind() const {
    return kind::metaKindOf(getKind());
  }

  /**
   * Returns the number of children this node has.
   *
   * @return the number of children
   */
  inline size_t getNumChildren() const;

  /**
   * If this is a CONST_* TypeNode, extract the constant from it.
   */
  template <class T>
  inline const T& getConst() const;

  /**
   * Returns the value of the given attribute that this has been attached.
   *
   * @param attKind the kind of the attribute
   * @return the value of the attribute
   */
  template <class AttrKind>
  inline typename AttrKind::value_type
  getAttribute(const AttrKind& attKind) const;

  // Note that there are two, distinct hasAttribute() declarations for
  // a reason (rather than using a pointer-valued argument with a
  // default value): they permit more optimized code in the underlying
  // hasAttribute() implementations.

  /**
   * Returns true if this node has been associated an attribute of
   * given kind.  Additionally, if a pointer to the value_kind is
   * give, and the attribute value has been set for this node, it will
   * be returned.
   *
   * @param attKind the kind of the attribute
   * @return true if this node has the requested attribute
   */
  template <class AttrKind>
  inline bool hasAttribute(const AttrKind& attKind) const;

  /**
   * Returns true if this node has been associated an attribute of given kind.
   * Additionaly, if a pointer to the value_kind is give, and the attribute
   * value has been set for this node, it will be returned.
   *
   * @param attKind the kind of the attribute
   * @param value where to store the value if it exists
   * @return true if this node has the requested attribute
   */
  template <class AttrKind>
  inline bool getAttribute(const AttrKind& attKind,
                           typename AttrKind::value_type& value) const;

  /**
   * Sets the given attribute of this node to the given value.
   *
   * @param attKind the kind of the atribute
   * @param value the value to set the attribute to
   */
  template <class AttrKind>
  inline void setAttribute(const AttrKind& attKind,
                           const typename AttrKind::value_type& value);

  /** Iterator allowing for scanning through the children. */
  typedef expr::NodeValue::iterator<TypeNode> iterator;
  /** Constant iterator allowing for scanning through the children. */
  typedef expr::NodeValue::iterator<TypeNode> const_iterator;

  /**
   * Returns the iterator pointing to the first child.
   *
   * @return the iterator
   */
  inline iterator begin() {
    return d_nv->begin<TypeNode>();
  }

  /**
   * Returns the iterator pointing to the end of the children (one
   * beyond the last one.
   *
   * @return the end of the children iterator.
   */
  inline iterator end() {
    return d_nv->end<TypeNode>();
  }

  /**
   * Returns the const_iterator pointing to the first child.
   *
   * @return the const_iterator
   */
  inline const_iterator begin() const {
    return d_nv->begin<TypeNode>();
  }

  /**
   * Returns the const_iterator pointing to the end of the children
   * (one beyond the last one.
   *
   * @return the end of the children const_iterator.
   */
  inline const_iterator end() const {
    return d_nv->end<TypeNode>();
  }

  /**
   * Converts this type into a string representation.
   *
   * @return the string representation of this type.
   */
  std::string toString() const;

  /**
   * Converts this node into a string representation and sends it to the
   * given stream
   *
   * @param out the stream to serialize this node to
   * @param language the language in which to output
   */
  inline void toStream(std::ostream& out) const {
    options::ioutils::Scope scope(out);
    options::ioutils::applyDagThresh(out, 0);
    d_nv->toStream(out);
  }

  /**
   * Very basic pretty printer for TypeNode.
   *
   * @param out output stream to print to.
   * @param indent number of spaces to indent the formula by.
   */
  void printAst(std::ostream& out, int indent = 0) const;

  /**
   * Returns true if this type is a null type.
   *
   * @return true if null
   */
  bool isNull() const {
    return d_nv == &expr::NodeValue::null();
  }

  /**
   * Returns the cardinality of this type.
   *
   * @return a finite or infinite cardinality
   */
  Cardinality getCardinality() const;
  /**
   * Get the cardinality class of this type node. The cardinality class
   * is static for each type node and does not depend on the state of the
   * solver. For details on cardinality classes, see util/cardinality_class.h
   *
   * @return the cardinality class
   */
  CardinalityClass getCardinalityClass();
  /**
   * Determine if the cardinality of this type is strictly less than `n`.
   * We do not want to compute the precise cardinality for this for performance
   * reasons, and will answer false if it is not less than or if we don't know.
   * @return if the cardinality of this type is strictly less than `n`.
   */
  bool isCardinalityLessThan(size_t n);

  /** is closed enumerable type
   *
   * This returns true if this type has an enumerator that produces constants
   * that are fully handled by cvc5's quantifier-free theory solvers. Examples
   * of types that are not closed enumerable are:
   * (1) uninterpreted sorts,
   * (2) arrays,
   * (3) codatatypes,
   * (4) functions,
   * (5) parametric sorts involving any of the above.
   */
  bool isClosedEnumerable();

  /**
   * Is this a first-class type?
   * First-class types are types for which:
   * (1) we handle equalities between terms of that type, and
   * (2) they are allowed to be parameters of parametric types (e.g. index or element types of arrays).
   *
   * Examples of types that are not first-class include constructor types,
   * selector types, tester types, regular expressions and SExprs.
   */
  bool isFirstClass() const;

  /**
   * Returns whether this type is well-founded.
   *
   * @return true iff the type is well-founded
   */
  bool isWellFounded() const;

  /** Is this the Boolean type? */
  bool isBoolean() const;

  /** Is this the Integer type? */
  bool isInteger() const;

  /** Is this the Real type? */
  bool isReal() const;

  /** Is this the String type? */
  bool isString() const;

  /** Is this a string-like type? (string or sequence) */
  bool isStringLike() const;

  /** Is this the integer or real type? */
  bool isRealOrInt() const;

  /** Is this the Rounding Mode type? */
  bool isRoundingMode() const;

  /** Is this an array type? */
  bool isArray() const;

  /** Is this a finite-field type? */
  bool isFiniteField() const;

  /** Is this a Set type? */
  bool isSet() const;

  /** Is this a Bag type? */
  bool isBag() const;

  /** Is this a Sequence type? */
  bool isSequence() const;

  /** Is this an abstract type? */
  bool isAbstract() const;

  /** Is this the fully abstract type? */
  bool isFullyAbstract() const;

  /** Get the index type (for array types) */
  TypeNode getArrayIndexType() const;

  /** Get the element type (for array types) */
  TypeNode getArrayConstituentType() const;

  /** Get the return type (for constructor types) */
  TypeNode getDatatypeConstructorRangeType() const;

  /** Get the domain type (for selector types) */
  TypeNode getDatatypeSelectorDomainType() const;

  /** Get the return type (for selector types) */
  TypeNode getDatatypeSelectorRangeType() const;

  /** Get the domain type (for tester types) */
  TypeNode getDatatypeTesterDomainType() const;

  /** Get the element type (for set types) */
  TypeNode getSetElementType() const;

  /** Get the element type (for bag types) */
  TypeNode getBagElementType() const;

  /** Get the element type (for sequence types) */
  TypeNode getSequenceElementType() const;

  /** Get the abstract kind (for abstract types) */
  Kind getAbstractedKind() const;

  /**
   * Is maybe kind. Return true if an instance of this type may have kind k.
   * This is true if the kind of this sort is k, or if it is a abstract type
   * whose abstracted kind is k or ABSTRACT_TYPE (the fully abstract type).
   *
   * For example:
   * isMaybeKind ? BITVECTOR_TYPE = true
   * isMaybeKind ? SET_TYPE = true
   * isMaybeKind ?Set SET_TYPE = true
   * isMaybeKind (Set Int) SET_TYPE = true
   * isMaybeKind (_ BitVec 4) SET_TYPE = false
   * isMaybeKind ?BitVec SET_TYPE = false
   */
  bool isMaybeKind(Kind k) const;

  /**
   * Is this a function type?  Function-like things (e.g. datatype
   * selectors) that aren't actually functions are NOT considered
   * functions, here.
   */
  bool isFunction() const;

  /**
   * Is this a function-LIKE type?  Function-like things
   * (e.g. datatype selectors) that aren't actually functions ARE
   * considered functions, here.  The main point is that this is used
   * to avoid anything higher-order: anything function-like cannot be
   * the argument or return value for anything else function-like.
   *
   * Arrays are explicitly *not* function-like for the purposes of
   * this test.  However, functions still cannot contain anything
   * function-like.
   */
  bool isFunctionLike() const;

  /**
   * Is instance of, returns true if this type is equivalent to the
   * leastUpperBound (see TypeNode::leastUpperBound) of itself and t.
   */
  bool isInstanceOf(const TypeNode& t) const;
  /**
   * Is comparable to type t, returns true if this type and t have a non-null
   * leastUpperBound (see TypeNode::leastUpperBound).
   */
  bool isComparableTo(const TypeNode& t) const;
  /**
   * Least upper bound with type.
   *
   * We consider a partial order on types such that T1 <= T2 if T2 is an
   * instance of T1.
   *
   * This returns the most specific type that is an instance
   * of both this and t, or null if this type and t are incompatible.
   *
   * For example:
   * ?BitVec <lub> ? = ?BitVec
   * (Array ?BitVec Int) <lub> (Array (_ BitVec 4) ?) = (Array (_ BitVec 4) Int)
   * (Array ? Int) <lub> (Array ? Real) = null.
   */
  TypeNode leastUpperBound(const TypeNode& t) const;
  /**
   * Greatest lower bound with type. The dual of leastUpperBound, for example:
   * ?BitVec <glb> ? = ?
   * (Array ?BitVec Int) <glb> (Array (_ BitVec 4) ?) = (Array ?BitVec ?)
   * (Array ? Int) <glb> (Array ? Real) = null.
   */
  TypeNode greatestLowerBound(const TypeNode& t) const;
  /**
   * Get the argument types of a function, datatype constructor,
   * datatype selector, or datatype tester.
   */
  std::vector<TypeNode> getArgTypes() const;

  /**
   * Get the types used to instantiate the type parameters of a parametric
   * type (parametric datatype or uninterpreted sort constructor type,
   * see TypeNode::instantiate(const std::vector<TypeNode>& const).
   *
   * Asserts that this type is an instantiated type.
   *
   * @return the types used to instantiate the type parameters of a
   *         parametric type
   */
  std::vector<TypeNode> getInstantiatedParamTypes() const;

  /**
   * Get the range type (i.e., the type of the result) of a function,
   * datatype constructor, datatype selector, or datatype tester.
   */
  TypeNode getRangeType() const;

  /**
   * Is this a predicate type?  NOTE: all predicate types are also
   * function types (so datatype testers are NOT considered
   * "predicates" for the purpose of this function).
   */
  bool isPredicate() const;

  /**
   * Is this a predicate-LIKE type?  Predicate-like things
   * (e.g. datatype testers) that aren't actually predicates ARE
   * considered predicates, here.
   *
   * Arrays are explicitly *not* predicate-like for the purposes of
   * this test.
   */
  bool isPredicateLike() const;

  /** Is this a tuple type? */
  bool isTuple() const;

  /** Is this a record type? */
  bool isRecord() const;

  /** Get the length of a tuple type */
  size_t getTupleLength() const;

  /** Get the constituent types of a tuple type */
  std::vector<TypeNode> getTupleTypes() const;

  /** Is this a regexp type */
  bool isRegExp() const;

  /** Is this a floating-point type */
  bool isFloatingPoint() const;

  /** Is this a floating-point type of with <code>exp</code> exponent bits
      and <code>sig</code> significand bits */
  bool isFloatingPoint(unsigned exp, unsigned sig) const;

  /** Is this a bit-vector type */
  bool isBitVector() const;

  /** Is this a bit-vector type of size <code>size</code> */
  bool isBitVector(unsigned size) const;

  /** Is this a datatype type */
  bool isDatatype() const;

  /** Is this a parameterized datatype type */
  bool isParametricDatatype() const;

  /** Is this a codatatype type */
  bool isCodatatype() const;

  /** Is this a fully instantiated datatype type */
  bool isInstantiatedDatatype() const;

  /**
   * Is this an uninterpreted sort constructed from instantiating an
   * uninterpreted sort constructor?
   */
  bool isInstantiatedUninterpretedSort() const;

  /**
   * Return true if this is an instantiated parametric datatype or
   * uninterpreted sort constructor type.
   */
  bool isInstantiated() const;

  /** Is this a sygus datatype type */
  bool isSygusDatatype() const;

  /**
   * Instantiate parametric type (parametric datatype or uninterpreted sort
   * constructor type).
   *
   * The parameter list of this type must be the same size as the list of
   * argument parameters `params`.
   *
   * If this TypeNode is a parametric datatype, this constructs the
   * instantiated version of this parametric datatype. For example, passing
   * (par (A) (List A)), { Int } ) to this method returns (List Int).
   *
   * If this is an uninterpreted sort constructor type, this constructs the
   * instantiated version of this sort constructor. For example, for a sort
   * constructor declared via (declare-sort U 2), passing { Int, Int } will
   * generate the instantiated sort (U Int Int).
   */
  TypeNode instantiate(const std::vector<TypeNode>& params) const;

  /** Is this an instantiated datatype parameter */
  bool isParameterInstantiatedDatatype(size_t n) const;

  /** Is this a datatype constructor type? */
  bool isDatatypeConstructor() const;

  /** Is this a datatype selector type? */
  bool isDatatypeSelector() const;

  /** Is this a datatype tester type? */
  bool isDatatypeTester() const;

  /** Is this a datatype updater type? */
  bool isDatatypeUpdater() const;

  /** Get the internal Datatype specification from a datatype type. */
  const DType& getDType() const;

  /** Get the exponent size of this floating-point type. */
  unsigned getFloatingPointExponentSize() const;

  /** Get the significand size of this floating-point type. */
  unsigned getFloatingPointSignificandSize() const;

  /** Get the size of this bit-vector type. */
  uint32_t getBitVectorSize() const;

  /** Get the field cardinality (order) of this finite-field type. */
  const Integer& getFfSize() const;

  /** Is this a sort kind? */
  bool isUninterpretedSort() const;

  /** Is this a sort constructor kind? */
  bool isUninterpretedSortConstructor() const;

  /** Get sort constructor arity. */
  uint64_t getUninterpretedSortConstructorArity() const;

  /** Is this an unresolved datatype? */
  bool isUnresolvedDatatype() const;
  /**
   * Has name? Return true if this node has an associated variable
   * name (via the attribute expr::VarNameAttr). This is true for
   * uninterpreted sorts and uninterpreted sort constructors.
   */
  bool hasName() const;
  /**
   * Get the name. Should only be called on nodes such that
   * hasName() returns true. Returns the string value of the
   * expr::VarNameAttr attribute for this node.
   */
  std::string getName() const;

  /**
   * Get the uninterpreted sort constructor type this instantiated
   * uninterpreted sort has been constructed from.
   *
   * Asserts that this is an instantiated uninterpreted sort.
   */
  TypeNode getUninterpretedSortConstructor() const;

 private:
  /** Unify internal, for computing leastUpperBound and greatestLowerBound */
  TypeNode unifyInternal(const TypeNode& t, bool isLub) const;
};/* class TypeNode */

/**
 * Serializes a given node to the given stream.
 *
 * @param out the output stream to use
 * @param n the node to output to the stream
 * @return the stream
 */
inline std::ostream& operator<<(std::ostream& out, const TypeNode& n) {
  n.toStream(out);
  return out;
}

}  // namespace cvc5::internal

namespace std {

template <>
struct hash<cvc5::internal::TypeNode>
{
  size_t operator()(const cvc5::internal::TypeNode& tn) const;
};

}  // namespace std

#include "expr/node_manager.h"

namespace cvc5::internal {

inline TypeNode
TypeNode::substitute(const TypeNode& type,
                     const TypeNode& replacement) const {
  std::unordered_map<TypeNode, TypeNode> cache;
  return substitute(type, replacement, cache);
}

template <class Iterator1, class Iterator2>
inline TypeNode
TypeNode::substitute(Iterator1 typesBegin,
                     Iterator1 typesEnd,
                     Iterator2 replacementsBegin,
                     Iterator2 replacementsEnd) const {
  std::unordered_map<TypeNode, TypeNode> cache;
  return substitute(typesBegin, typesEnd,
                    replacementsBegin, replacementsEnd, cache);
}

template <class Iterator1, class Iterator2>
TypeNode TypeNode::substitute(
    Iterator1 typesBegin,
    Iterator1 typesEnd,
    Iterator2 replacementsBegin,
    Iterator2 replacementsEnd,
    std::unordered_map<TypeNode, TypeNode>& cache) const
{
  // in cache?
  std::unordered_map<TypeNode, TypeNode>::const_iterator i = cache.find(*this);
  if(i != cache.end()) {
    return (*i).second;
  }

  // otherwise compute
  Assert(typesEnd - typesBegin == replacementsEnd - replacementsBegin)
      << "Substitution iterator ranges must be equal size";
  Iterator1 j = find(typesBegin, typesEnd, *this);
  if(j != typesEnd) {
    TypeNode tn = *(replacementsBegin + (j - typesBegin));
    cache[*this] = tn;
    return tn;
  } else if(getNumChildren() == 0) {
    cache[*this] = *this;
    return *this;
  } else {
    NodeBuilder nb(getKind());
    if(getMetaKind() == kind::metakind::PARAMETERIZED) {
      // push the operator
      nb << TypeNode(d_nv->d_children[0]);
    }
    for (const TypeNode& tn : *this)
    {
      nb << tn.substitute(
          typesBegin, typesEnd, replacementsBegin, replacementsEnd, cache);
    }
    TypeNode tn = nb.constructTypeNode();
    cache[*this] = tn;
    return tn;
  }
}

inline size_t TypeNode::getNumChildren() const {
  return d_nv->getNumChildren();
}

template <class T>
inline const T& TypeNode::getConst() const {
  return d_nv->getConst<T>();
}

inline TypeNode::TypeNode(const expr::NodeValue* ev) :
  d_nv(const_cast<expr::NodeValue*> (ev)) {
  Assert(d_nv != NULL) << "Expecting a non-NULL expression value!";
  d_nv->inc();
}

inline TypeNode::TypeNode(const TypeNode& typeNode) {
  Assert(typeNode.d_nv != NULL) << "Expecting a non-NULL expression value!";
  d_nv = typeNode.d_nv;
  d_nv->inc();
}

inline TypeNode::~TypeNode() {
  Assert(d_nv != NULL) << "Expecting a non-NULL expression value!";
  d_nv->dec();
}

inline void TypeNode::assignNodeValue(expr::NodeValue* ev) {
  d_nv = ev;
  d_nv->inc();
}

inline TypeNode& TypeNode::operator=(const TypeNode& typeNode) {
  Assert(d_nv != NULL) << "Expecting a non-NULL expression value!";
  Assert(typeNode.d_nv != NULL)
      << "Expecting a non-NULL expression value on RHS!";
  if(__builtin_expect( ( d_nv != typeNode.d_nv ), true )) {
    d_nv->dec();
    d_nv = typeNode.d_nv;
    d_nv->inc();
  }
  return *this;
}

template <class AttrKind>
inline typename AttrKind::value_type TypeNode::
getAttribute(const AttrKind&) const {
  return NodeManager::currentNM()->getAttribute(d_nv, AttrKind());
}

template <class AttrKind>
inline bool TypeNode::
hasAttribute(const AttrKind&) const {
  return NodeManager::currentNM()->hasAttribute(d_nv, AttrKind());
}

template <class AttrKind>
inline bool TypeNode::getAttribute(const AttrKind&, typename AttrKind::value_type& ret) const {
  return NodeManager::currentNM()->getAttribute(d_nv, AttrKind(), ret);
}

template <class AttrKind>
inline void TypeNode::
setAttribute(const AttrKind&, const typename AttrKind::value_type& value) {
  NodeManager::currentNM()->setAttribute(d_nv, AttrKind(), value);
}

inline void TypeNode::printAst(std::ostream& out, int indent) const {
  d_nv->printAst(out, indent);
}

inline bool TypeNode::isBoolean() const {
  return
    ( getKind() == kind::TYPE_CONSTANT && getConst<TypeConstant>() == BOOLEAN_TYPE );
}

inline bool TypeNode::isString() const {
  return getKind() == kind::TYPE_CONSTANT &&
    getConst<TypeConstant>() == STRING_TYPE;
}

/** Is this a regexp type */
inline bool TypeNode::isRegExp() const {
  return getKind() == kind::TYPE_CONSTANT &&
    getConst<TypeConstant>() == REGEXP_TYPE;
 }

inline bool TypeNode::isRoundingMode() const {
  return getKind() == kind::TYPE_CONSTANT &&
    getConst<TypeConstant>() == ROUNDINGMODE_TYPE;
}

inline bool TypeNode::isArray() const {
  return getKind() == kind::ARRAY_TYPE;
}

inline bool TypeNode::isFiniteField() const
{
  return getKind() == kind::FINITE_FIELD_TYPE;
}

inline TypeNode TypeNode::getArrayIndexType() const {
  Assert(isArray());
  return (*this)[0];
}

inline TypeNode TypeNode::getArrayConstituentType() const {
  Assert(isArray());
  return (*this)[1];
}

inline TypeNode TypeNode::getDatatypeConstructorRangeType() const
{
  Assert(isDatatypeConstructor());
  return (*this)[getNumChildren()-1];
}

inline TypeNode TypeNode::getDatatypeSelectorDomainType() const
{
  Assert(isDatatypeSelector());
  return (*this)[0];
}

inline TypeNode TypeNode::getDatatypeSelectorRangeType() const
{
  Assert(isDatatypeSelector());
  return (*this)[1];
}

inline bool TypeNode::isSet() const {
  return getKind() == kind::SET_TYPE;
}

inline bool TypeNode::isSequence() const
{
  return getKind() == kind::SEQUENCE_TYPE;
}

inline TypeNode TypeNode::getSetElementType() const {
  Assert(isSet());
  return (*this)[0];
}

inline bool TypeNode::isFunction() const {
  return getKind() == kind::FUNCTION_TYPE;
}

inline bool TypeNode::isFunctionLike() const {
  return
    getKind() == kind::FUNCTION_TYPE ||
    getKind() == kind::CONSTRUCTOR_TYPE ||
    getKind() == kind::SELECTOR_TYPE ||
    getKind() == kind::TESTER_TYPE;
}

inline bool TypeNode::isPredicate() const {
  return isFunction() && getRangeType().isBoolean();
}

inline bool TypeNode::isPredicateLike() const {
  return isFunctionLike() && getRangeType().isBoolean();
}

}  // namespace cvc5::internal

#endif /* CVC5__NODE_H */
