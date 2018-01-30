/*********************                                                        */
/*! \file normal_form.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__NORMAL_FORM_H
#define __CVC4__THEORY__ARITH__NORMAL_FORM_H

#include <algorithm>
#include <list>

#include "base/output.h"
#include "expr/node.h"
#include "expr/node_self_iterator.h"
#include "theory/arith/delta_rational.h"
#include "util/rational.h"


namespace CVC4 {
namespace theory {
namespace arith {

/***********************************************/
/***************** Normal Form *****************/
/***********************************************/
/***********************************************/

/**
 * Section 1: Languages
 * The normal form for arithmetic nodes is defined by the language
 * accepted by the following BNFs with some guard conditions.
 * (The guard conditions are in Section 3 for completeness.)
 *
 * variable := n
 *   where
 *     n.isVar() or is foreign
 *     n.getType() \in {Integer, Real}
 *
 * constant := n
 *   where
 *     n.getKind() == kind::CONST_RATIONAL
 *
 * var_list := variable | (* [variable])
 *   where
 *     len [variable] >= 2
 *     isSorted varOrder [variable]
 *
 * monomial := constant | var_list | (* constant' var_list')
 *   where
 *     \f$ constant' \not\in {0,1} \f$
 *
 * polynomial := monomial' | (+ [monomial])
 *   where
 *     len [monomial] >= 2
 *     isStrictlySorted monoOrder [monomial]
 *     forall (\x -> x != 0) [monomial]
 *
 * rational_cmp := (|><| qpolynomial constant)
 *   where
 *     |><| is GEQ, or GT
 *     not (exists constantMonomial (monomialList qpolynomial))
 *     (exists realMonomial (monomialList qpolynomial))
 *     abs(monomialCoefficient (head (monomialList qpolynomial))) == 1
 *
 * integer_cmp := (>= zpolynomial constant)
 *   where
 *     not (exists constantMonomial (monomialList zpolynomial))
 *     (forall integerMonomial (monomialList zpolynomial))
 *     the gcd of all numerators of coefficients is 1
 *     the denominator of all coefficients and the constant is 1
 *     the leading coefficient is positive
 *
 * rational_eq := (= qvarlist qpolynomial)
 *   where
 *     let allMonomials = (cons qvarlist (monomialList zpolynomial))
 *     let variableMonomials = (drop constantMonomial allMonomials)
 *     isStrictlySorted variableMonomials
 *     exists realMonomial variableMonomials
 *     is not empty qvarlist
 *
 * integer_eq := (= zmonomial zpolynomial)
 *   where
 *     let allMonomials = (cons zmonomial (monomialList zpolynomial))
 *     let variableMonomials = (drop constantMonomial allMonomials)
 *     not (constantMonomial zmonomial)
 *     (forall integerMonomial allMonomials)
 *     isStrictlySorted variableMonomials
 *     the gcd of all numerators of coefficients is 1
 *     the denominator of all coefficients and the constant is 1
 *     the coefficient of monomial is positive
 *     the value of the coefficient of monomial is minimal in variableMonomials
 *
 * comparison := TRUE | FALSE
 *   | rational_cmp | (not rational_cmp)
 *   | rational_eq | (not rational_eq)
 *   | integer_cmp | (not integer_cmp)
 *   | integer_eq | (not integer_eq)
 *
 * Normal Form for terms := polynomial
 * Normal Form for atoms := comparison
 */

/**
 * Section 2: Helper Classes
 * The langauges accepted by each of these defintions
 * roughly corresponds to one of the following helper classes:
 *  Variable
 *  Constant
 *  VarList
 *  Monomial
 *  Polynomial
 *  Comparison
 *
 * Each of the classes obeys the following contracts/design decisions:
 * -Calling isMember(Node node) on a node returns true iff that node is a
 *  a member of the language. Note: isMember is O(n).
 * -Calling isNormalForm() on a helper class object returns true iff that
 *  helper class currently represents a normal form object.
 * -If isNormalForm() is false, then this object must have been made
 *  using a mk*() factory function.
 * -If isNormalForm() is true, calling getNode() on all of these classes
 *  returns a node that would be accepted by the corresponding language.
 *  And if isNormalForm() is false, returns Node::null().
 * -Each of the classes is immutable.
 * -Public facing constuctors have a 1-to-1 correspondence with one of
 *  production rules in the above grammar.
 * -Public facing constuctors are required to fail in debug mode when the
 *  guards of the production rule are not strictly met.
 *  For example: Monomial(Constant(1),VarList(Variable(x))) must fail.
 * -When a class has a Class parseClass(Node node) function,
 *  if isMember(node) is true, the function is required to return an instance
 *  of the helper class, instance, s.t. instance.getNode() == node.
 *  And if isMember(node) is false, this throws an assertion failure in debug
 *  mode and has undefined behaviour if not in debug mode.
 * -Only public facing constructors, parseClass(node), and mk*() functions are
 *  considered privileged functions for the helper class.
 * -Only privileged functions may use private constructors, and access
 *  private data members.
 * -All non-privileged functions are considered utility functions and
 *  must use a privileged function in order to create an instance of the class.
 */

/**
 * Section 3: Guard Conditions Misc.
 *
 *
 *  variable_order x y =
 *    if (meta_kind_variable x) and (meta_kind_variable y)
 *    then node_order x y
 *    else if (meta_kind_variable x)
 *    then false
 *    else if (meta_kind_variable y)
 *    then true
 *    else node_order x y
 *
 *  var_list_len vl =
 *    match vl with
 *       variable -> 1
 *     | (* [variable]) -> len [variable]
 *
 *  order res =
 *    match res with
 *       Empty -> (0,Node::null())
 *     | NonEmpty(vl) -> (var_list_len vl, vl)
 *
 *  var_listOrder a b = tuple_cmp (order a) (order b)
 *
 *  monomialVarList monomial =
 *    match monomial with
 *        constant -> Empty
 *      | var_list -> NonEmpty(var_list)
 *      | (* constant' var_list') -> NonEmpty(var_list')
 *
 *  monoOrder m0 m1 = var_listOrder (monomialVarList m0) (monomialVarList m1)
 *
 *  integerMonomial mono =
 *    forall varHasTypeInteger (monomialVarList mono)
 *
 *  realMonomial mono = not (integerMonomial mono)
 *
 *  constantMonomial monomial =
 *    match monomial with
 *        constant -> true
 *      | var_list -> false
 *      | (* constant' var_list') -> false
 *
 *  monomialCoefficient monomial =
 *    match monomial with
 *        constant -> constant
 *      | var_list -> Constant(1)
 *      | (* constant' var_list') -> constant'
 *
 *  monomialList polynomial =
 *    match polynomial with
 *        monomial -> monomial::[]
 *      | (+ [monomial]) -> [monomial]
 */

/**
 * A NodeWrapper is a class that is a thinly veiled container of a Node object.
 */
class NodeWrapper {
private:
  Node node;
public:
  NodeWrapper(Node n) : node(n) {}
  const Node& getNode() const { return node; }
};/* class NodeWrapper */


class Variable : public NodeWrapper {
public:
  Variable(Node n) : NodeWrapper(n) {
    Assert(isMember(getNode()));
  }

  // TODO: check if it's a theory leaf also
  static bool isMember(Node n) {
    Kind k = n.getKind();
    switch(k){
    case kind::CONST_RATIONAL:
      return false;
    case kind::INTS_DIVISION:
    case kind::INTS_MODULUS:
    case kind::DIVISION:
    case kind::INTS_DIVISION_TOTAL:
    case kind::INTS_MODULUS_TOTAL:
    case kind::DIVISION_TOTAL:
      return isDivMember(n);
    case kind::EXPONENTIAL:
    case kind::SINE:
    case kind::COSINE:
    case kind::TANGENT:
    case kind::COSECANT:
    case kind::SECANT:
    case kind::COTANGENT:
    case kind::ARCSINE:
    case kind::ARCCOSINE:
    case kind::ARCTANGENT:
    case kind::ARCCOSECANT:
    case kind::ARCSECANT:
    case kind::ARCCOTANGENT:
    case kind::SQRT:
    case kind::PI:
      return isTranscendentalMember(n);      
    case kind::ABS:
    case kind::TO_INTEGER:
      // Treat to_int as a variable; it is replaced in early preprocessing
      // by a variable.
      return true;
    default:
      return isLeafMember(n);
    }
  }

  static bool isLeafMember(Node n);
  static bool isDivMember(Node n);
  bool isDivLike() const{
    return isDivMember(getNode());
  }
  static bool isTranscendentalMember(Node n);

  bool isNormalForm() { return isMember(getNode()); }

  bool isIntegral() const {
    return getNode().getType().isInteger();
  }

  bool isMetaKindVariable() const {
    return getNode().isVar();
  }

  bool operator<(const Variable& v) const {
    VariableNodeCmp cmp;
    return cmp(this->getNode(), v.getNode());
  }

  struct VariableNodeCmp {
    static inline int cmp(const Node& n, const Node& m) {
      if ( n == m ) { return 0; }

      // this is now slightly off of the old variable order.

      bool nIsInteger = n.getType().isInteger();
      bool mIsInteger = m.getType().isInteger();

      if(nIsInteger == mIsInteger){
        bool nIsVariable = n.isVar();
        bool mIsVariable = m.isVar();

        if(nIsVariable == mIsVariable){
          if(n < m){
            return -1;
          }else{
            Assert( n != m );
            return 1;
          }
        }else{
          if(nIsVariable){
            return -1; // nIsVariable => !mIsVariable
          }else{
            return 1; // !nIsVariable => mIsVariable
          }
        }
      }else{
        Assert(nIsInteger != mIsInteger);
        if(nIsInteger){
          return 1; // nIsInteger => !mIsInteger
        }else{
          return -1; // !nIsInteger => mIsInteger
        }
      }
    }

    bool operator()(const Node& n, const Node& m) const {
      return VariableNodeCmp::cmp(n,m) < 0;
    }
  };

  bool operator==(const Variable& v) const { return getNode() == v.getNode();}

  size_t getComplexity() const;
};/* class Variable */


class Constant : public NodeWrapper {
public:
  Constant(Node n) : NodeWrapper(n) {
    Assert(isMember(getNode()));
  }

  static bool isMember(Node n) {
    return n.getKind() == kind::CONST_RATIONAL;
  }

  bool isNormalForm() { return isMember(getNode()); }

  static Constant mkConstant(Node n) {
    Assert(n.getKind() == kind::CONST_RATIONAL);
    return Constant(n);
  }

  static Constant mkConstant(const Rational& rat);

  static Constant mkZero() {
    return mkConstant(Rational(0));
  }

  static Constant mkOne() {
    return mkConstant(Rational(1));
  }

  const Rational& getValue() const {
    return getNode().getConst<Rational>();
  }

  static int absCmp(const Constant& a, const Constant& b);
  bool isIntegral() const { return getValue().isIntegral(); }

  int sgn() const { return getValue().sgn(); }

  bool isZero() const { return sgn() == 0; }
  bool isNegative() const { return sgn() < 0; }
  bool isPositive() const { return sgn() > 0; }

  bool isOne() const { return getValue() == 1; }

  Constant operator*(const Rational& other) const {
    return mkConstant(getValue() * other);
  }

  Constant operator*(const Constant& other) const {
    return mkConstant(getValue() * other.getValue());
  }
  Constant operator+(const Constant& other) const {
    return mkConstant(getValue() + other.getValue());
  }
  Constant operator-() const {
    return mkConstant(-getValue());
  }

  Constant inverse() const{
    Assert(!isZero());
    return mkConstant(getValue().inverse());
  }

  bool operator<(const Constant& other) const {
    return getValue() < other.getValue();
  }

  bool operator==(const Constant& other) const {
    //Rely on node uniqueness.
    return getNode() == other.getNode();
  }

  Constant abs() const {
    if(isNegative()){
      return -(*this);
    }else{
      return (*this);
    }
  }

  uint32_t length() const{
    Assert(isIntegral());
    return getValue().getNumerator().length();
  }

  size_t getComplexity() const;

};/* class Constant */


template <class GetNodeIterator>
inline Node makeNode(Kind k, GetNodeIterator start, GetNodeIterator end) {
  NodeBuilder<> nb(k);

  while(start != end) {
    nb << (*start).getNode();
    ++start;
  }

  return Node(nb);
}/* makeNode<GetNodeIterator>(Kind, iterator, iterator) */

/**
 * A VarList is a sorted list of variables representing a product.
 * If the VarList is empty, it represents an empty product or 1.
 * If the VarList has size 1, it represents a single variable.
 *
 * A non-sorted VarList can never be successfully made in debug mode.
 */
class VarList : public NodeWrapper {
private:

  static Node multList(const std::vector<Variable>& list) {
    Assert(list.size() >= 2);

    return makeNode(kind::NONLINEAR_MULT, list.begin(), list.end());
  }

  VarList() : NodeWrapper(Node::null()) {}

  VarList(Node n);

  typedef expr::NodeSelfIterator internal_iterator;

  internal_iterator internalBegin() const {
    if(singleton()){
      return expr::NodeSelfIterator::self(getNode());
    }else{
      return getNode().begin();
    }
  }

  internal_iterator internalEnd() const {
    if(singleton()){
      return expr::NodeSelfIterator::selfEnd(getNode());
    }else{
      return getNode().end();
    }
  }

public:

  class iterator : public std::iterator<std::input_iterator_tag, Variable> {
  private:
    internal_iterator d_iter;

  public:
    explicit iterator(internal_iterator i) : d_iter(i) {}

    inline Variable operator*() {
      return Variable(*d_iter);
    }

    bool operator==(const iterator& i) {
      return d_iter == i.d_iter;
    }

    bool operator!=(const iterator& i) {
      return d_iter != i.d_iter;
    }

    iterator operator++() {
      ++d_iter;
      return *this;
    }

    iterator operator++(int) {
      return iterator(d_iter++);
    }
  };

  iterator begin() const {
    return iterator(internalBegin());
  }

  iterator end() const {
    return iterator(internalEnd());
  }

  Variable getHead() const {
    Assert(!empty());
    return *(begin());
  }

  VarList(Variable v) : NodeWrapper(v.getNode()) {
    Assert(isSorted(begin(), end()));
  }

  VarList(const std::vector<Variable>& l) : NodeWrapper(multList(l)) {
    Assert(l.size() >= 2);
    Assert(isSorted(begin(), end()));
  }

  static bool isMember(Node n);

  bool isNormalForm() const {
    return !empty();
  }

  static VarList mkEmptyVarList() {
    return VarList();
  }


  /** There are no restrictions on the size of l */
  static VarList mkVarList(const std::vector<Variable>& l) {
    if(l.size() == 0) {
      return mkEmptyVarList();
    } else if(l.size() == 1) {
      return VarList((*l.begin()).getNode());
    } else {
      return VarList(l);
    }
  }

  bool empty() const { return getNode().isNull(); }
  bool singleton() const {
    return !empty() && getNode().getKind() != kind::NONLINEAR_MULT;
  }

  int size() const {
    if(singleton())
      return 1;
    else
      return getNode().getNumChildren();
  }

  static VarList parseVarList(Node n);

  VarList operator*(const VarList& vl) const;

  int cmp(const VarList& vl) const;

  bool operator<(const VarList& vl) const { return cmp(vl) < 0; }

  bool operator==(const VarList& vl) const { return cmp(vl) == 0; }

  bool isIntegral() const {
    for(iterator i = begin(), e=end(); i != e; ++i ){
      Variable var = *i;
      if(!var.isIntegral()){
        return false;
      }
    }
    return true;
  }
  size_t getComplexity() const;

private:
  bool isSorted(iterator start, iterator end);

};/* class VarList */


/** Constructors have side conditions. Use the static mkMonomial functions instead. */ 
class Monomial : public NodeWrapper {
private:
  Constant constant;
  VarList varList;
  Monomial(Node n, const Constant& c, const VarList& vl):
    NodeWrapper(n), constant(c), varList(vl)
  {
    Assert(!c.isZero() ||  vl.empty() );
    Assert( c.isZero() || !vl.empty() );

    Assert(!c.isOne() || !multStructured(n));
  }

  static Node makeMultNode(const Constant& c, const VarList& vl) {
    Assert(!c.isZero());
    Assert(!c.isOne());
    Assert(!vl.empty());
    return NodeManager::currentNM()->mkNode(kind::MULT, c.getNode(), vl.getNode());
  }

  static bool multStructured(Node n) {
    return n.getKind() ==  kind::MULT &&
      n[0].getKind() == kind::CONST_RATIONAL &&
      n.getNumChildren() == 2;
  }

  Monomial(const Constant& c):
    NodeWrapper(c.getNode()), constant(c), varList(VarList::mkEmptyVarList())
  { }
  
  Monomial(const VarList& vl):
    NodeWrapper(vl.getNode()), constant(Constant::mkConstant(1)), varList(vl)
  {
    Assert( !varList.empty() );
  }

  Monomial(const Constant& c, const VarList& vl):
    NodeWrapper(makeMultNode(c,vl)), constant(c), varList(vl)
  {
    Assert( !c.isZero() );
    Assert( !c.isOne() );
    Assert( !varList.empty() );

    Assert(multStructured(getNode()));
  }
public:
  static bool isMember(TNode n);

  /** Makes a monomial with no restrictions on c and vl. */
  static Monomial mkMonomial(const Constant& c, const VarList& vl);

  /** If vl is empty, this make one. */
  static Monomial mkMonomial(const VarList& vl);

  static Monomial mkMonomial(const Constant& c){
    return Monomial(c);
  }
  
  static Monomial mkMonomial(const Variable& v){
    return Monomial(VarList(v));
  }

  static Monomial parseMonomial(Node n);

  static Monomial mkZero() {
    return Monomial(Constant::mkConstant(0));
  }
  static Monomial mkOne() {
    return Monomial(Constant::mkConstant(1));
  }
  const Constant& getConstant() const { return constant; }
  const VarList& getVarList() const { return varList; }
  
  bool isConstant() const {
    return varList.empty();
  }

  bool isZero() const {
    return constant.isZero();
  }

  bool coefficientIsOne() const {
    return constant.isOne();
  }

  bool absCoefficientIsOne() const {
    return coefficientIsOne() || constant.getValue() == -1;
  }

  bool constantIsPositive() const {
    return getConstant().isPositive();
  }

  Monomial operator*(const Rational& q) const;
  Monomial operator*(const Constant& c) const;
  Monomial operator*(const Monomial& mono) const;

  Monomial operator-() const{
    return (*this) * Rational(-1);
  }


  int cmp(const Monomial& mono) const {
    return getVarList().cmp(mono.getVarList());
  }

  bool operator<(const Monomial& vl) const {
    return cmp(vl) < 0;
  }

  bool operator==(const Monomial& vl) const {
    return cmp(vl) == 0;
  }

  static bool isSorted(const std::vector<Monomial>& m) {
    return std::is_sorted(m.begin(), m.end());
  }

  static bool isStrictlySorted(const std::vector<Monomial>& m) {
    return isSorted(m) && std::adjacent_find(m.begin(),m.end()) == m.end();
  }

  static void sort(std::vector<Monomial>& m);
  static void combineAdjacentMonomials(std::vector<Monomial>& m);

  /**
   * The variable product
   */
  bool integralVariables() const {
    return getVarList().isIntegral();
  }

  /**
   * The coefficient of the monomial is integral.
   */
  bool integralCoefficient() const {
    return getConstant().isIntegral();
  }

  /**
   * A Monomial is an "integral" monomial if the constant is integral.
   */
  bool isIntegral() const {
    return integralCoefficient() && integralVariables();
  }

  /** Returns true if the VarList is a product of at least 2 Variables.*/
  bool isNonlinear() const {
    return getVarList().size() >= 2;
  }

  /**
   * Given a sorted list of monomials, this function transforms this
   * into a strictly sorted list of monomials that does not contain zero.
   */
  //static std::vector<Monomial> sumLikeTerms(const std::vector<Monomial>& monos);

  int absCmp(const Monomial& other) const{
    return getConstant().getValue().absCmp(other.getConstant().getValue());
  }
  // bool absLessThan(const Monomial& other) const{
  //   return getConstant().abs() < other.getConstant().abs();
  // }

  uint32_t coefficientLength() const{
    return getConstant().length();
  }

  void print() const;
  static void printList(const std::vector<Monomial>& list);

  size_t getComplexity() const;
};/* class Monomial */

class SumPair;
class Comparison;;

class Polynomial : public NodeWrapper {
private:
  bool d_singleton;

  Polynomial(TNode n) : NodeWrapper(n), d_singleton(Monomial::isMember(n)) {
    Assert(isMember(getNode()));
  }

  static Node makePlusNode(const std::vector<Monomial>& m) {
    Assert(m.size() >= 2);

    return makeNode(kind::PLUS, m.begin(), m.end());
  }

  typedef expr::NodeSelfIterator internal_iterator;

  internal_iterator internalBegin() const {
    if(singleton()){
      return expr::NodeSelfIterator::self(getNode());
    }else{
      return getNode().begin();
    }
  }

  internal_iterator internalEnd() const {
    if(singleton()){
      return expr::NodeSelfIterator::selfEnd(getNode());
    }else{
      return getNode().end();
    }
  }

  bool singleton() const { return d_singleton; }

public:
  static bool isMember(TNode n);

  class iterator : public std::iterator<std::input_iterator_tag, Monomial> {
  private:
    internal_iterator d_iter;

  public:
    explicit iterator(internal_iterator i) : d_iter(i) {}

    inline Monomial operator*() {
      return Monomial::parseMonomial(*d_iter);
    }

    bool operator==(const iterator& i) {
      return d_iter == i.d_iter;
    }

    bool operator!=(const iterator& i) {
      return d_iter != i.d_iter;
    }

    iterator operator++() {
      ++d_iter;
      return *this;
    }

    iterator operator++(int) {
      return iterator(d_iter++);
    }
  };

  iterator begin() const { return iterator(internalBegin()); }
  iterator end() const {  return iterator(internalEnd()); }

  Polynomial(const Monomial& m):
    NodeWrapper(m.getNode()), d_singleton(true)
  {}

  Polynomial(const std::vector<Monomial>& m):
    NodeWrapper(makePlusNode(m)), d_singleton(false)
  {
    Assert( m.size() >= 2);
    Assert( Monomial::isStrictlySorted(m) );
  }

  static Polynomial mkPolynomial(const Constant& c){
    return Polynomial(Monomial::mkMonomial(c));
  }

  static Polynomial mkPolynomial(const Variable& v){
    return Polynomial(Monomial::mkMonomial(v));
  }

  static Polynomial mkPolynomial(const std::vector<Monomial>& m) {
    if(m.size() == 0) {
      return Polynomial(Monomial::mkZero());
    } else if(m.size() == 1) {
      return Polynomial((*m.begin()));
    } else {
      return Polynomial(m);
    }
  }

  static Polynomial parsePolynomial(Node n) {
    return Polynomial(n);
  }

  static Polynomial mkZero() {
    return Polynomial(Monomial::mkZero());
  }
  static Polynomial mkOne() {
    return Polynomial(Monomial::mkOne());
  }
  bool isZero() const {
    return singleton() && (getHead().isZero());
  }

  bool isConstant() const {
    return singleton() && (getHead().isConstant());
  }

  bool containsConstant() const {
    return getHead().isConstant();
  }

  uint32_t size() const{
    if(singleton()){
      return 1;
    }else{
      Assert(getNode().getKind() == kind::PLUS);
      return getNode().getNumChildren();
    }
  }

  Monomial getHead() const {
    return *(begin());
  }

  Polynomial getTail() const {
    Assert(! singleton());

    iterator tailStart = begin();
    ++tailStart;
    std::vector<Monomial> subrange;
    std::copy(tailStart, end(), std::back_inserter(subrange));
    return mkPolynomial(subrange);
  }

  Monomial minimumVariableMonomial() const;
  bool variableMonomialAreStrictlyGreater(const Monomial& m) const;

  void printList() const {
    if(Debug.isOn("normal-form")){
      Debug("normal-form") << "start list" << std::endl;
      for(iterator i = begin(), oend = end(); i != oend; ++i) {
        const Monomial& m =*i;
        m.print();
      }
      Debug("normal-form") << "end list" << std::endl;
    }
  }

  /** A Polynomial is an "integral" polynomial if all of the monomials are integral. */
  bool allIntegralVariables() const {
    for(iterator i = begin(), e=end(); i!=e; ++i){
      if(!(*i).integralVariables()){
        return false;
      }
    }
    return true;
  }

  /**
   * A Polynomial is an "integral" polynomial if all of the monomials are integral
   * and all of the coefficients are Integral. */
  bool isIntegral() const {
    for(iterator i = begin(), e=end(); i!=e; ++i){
      if(!(*i).isIntegral()){
        return false;
      }
    }
    return true;
  }

  static Polynomial sumPolynomials(const std::vector<Polynomial>& polynomials);

  /** Returns true if the polynomial contains a non-linear monomial.*/
  bool isNonlinear() const;


  /**
   * Selects a minimal monomial in the polynomial by the absolute value of
   * the coefficient.
   */
  Monomial selectAbsMinimum() const;

  /** Returns true if the absolute value of the head coefficient is one. */
  bool leadingCoefficientIsAbsOne() const;
  bool leadingCoefficientIsPositive() const;
  bool denominatorLCMIsOne() const;
  bool numeratorGCDIsOne() const;

  bool signNormalizedReducedSum() const {
    return leadingCoefficientIsPositive() && denominatorLCMIsOne() && numeratorGCDIsOne();
  }

  /**
   * Returns the Least Common Multiple of the denominators of the coefficients
   * of the monomials.
   */
  Integer denominatorLCM() const;

  /**
   * Returns the GCD of the numerators of the monomials.
   * Requires this to be an isIntegral() polynomial.
   */
  Integer numeratorGCD() const;

  /**
   * Returns the GCD of the coefficients of the monomials.
   * Requires this to be an isIntegral() polynomial.
   */
  Integer gcd() const;

  /** z must divide all of the coefficients of the polynomial. */
  Polynomial exactDivide(const Integer& z) const;

  Polynomial operator+(const Polynomial& vl) const;
  Polynomial operator-(const Polynomial& vl) const;
  Polynomial operator-() const{
    return (*this) * Rational(-1);
  }

  Polynomial operator*(const Rational& q) const;
  Polynomial operator*(const Constant& c) const;
  Polynomial operator*(const Monomial& mono) const;

  Polynomial operator*(const Polynomial& poly) const;

  /**
   * Viewing the integer polynomial as a list [(* coeff_i mono_i)]
   * The quotient and remainder of p divided by the non-zero integer z is:
   *   q := [(* floor(coeff_i/z) mono_i )]
   *   r := [(* rem(coeff_i/z) mono_i)]
   * computeQR(p,z) returns the node (+ q r).
   *
   * q and r are members of the Polynomial class.
   * For example:
   * computeQR( p = (+ 5 (* 3 x) (* 8 y)) , z = 2) returns
   *   (+ (+ 2 x (* 4 y)) (+ 1 x))
   */
  static Node computeQR(const Polynomial& p, const Integer& z);

  /** Returns the coefficient associated with the VarList in the polynomial. */
  Constant getCoefficient(const VarList& vl) const;

  uint32_t maxLength() const{
    iterator i = begin(), e=end();
    if( i == e){
      return 1;
    }else{
      uint32_t max = (*i).coefficientLength();
      ++i;
      for(; i!=e; ++i){
        uint32_t curr = (*i).coefficientLength();
        if(curr > max){
          max = curr;
        }
      }
      return max;
    }
  }

  uint32_t numMonomials() const {
    if( getNode().getKind() == kind::PLUS ){
      return getNode().getNumChildren();
    }else if(isZero()){
      return 0;
    }else{
      return 1;
    }
  }

  const Rational& asConstant() const{
    Assert(isConstant());
    return getNode().getConst<Rational>();
    //return getHead().getConstant().getValue();
  }

  bool isVarList() const {
    if(singleton()){
      return VarList::isMember(getNode());
    }else{
      return false;
    }
  }

  VarList asVarList() const {
    Assert(isVarList());
    return getHead().getVarList();
  }

  size_t getComplexity() const;

  friend class SumPair;
  friend class Comparison;

  /** Returns a node that if asserted ensures v is the abs of this polynomial.*/
  Node makeAbsCondition(Variable v){
    return makeAbsCondition(v, *this);
  }

  /** Returns a node that if asserted ensures v is the abs of p.*/
  static Node makeAbsCondition(Variable v, Polynomial p);

};/* class Polynomial */


/**
 * SumPair is a utility class that extends polynomials for use in computations.
 * A SumPair is always a combination of (+ p c) where
 *  c is a constant and p is a polynomial such that p = 0 or !p.containsConstant().
 *
 * These are a useful utility for representing the equation p = c as (+ p -c) where the pair
 * is known to implicitly be equal to 0.
 *
 * SumPairs do not have unique representations due to the potential for p = 0.
 * This makes them inappropriate for normal forms.
 */
class SumPair : public NodeWrapper {
private:
  static Node toNode(const Polynomial& p, const Constant& c){
    return NodeManager::currentNM()->mkNode(kind::PLUS, p.getNode(), c.getNode());
  }

  SumPair(TNode n) :
    NodeWrapper(n)
  {
    Assert(isNormalForm());
  }

public:

  SumPair(const Polynomial& p):
    NodeWrapper(toNode(p, Constant::mkConstant(0)))
  {
    Assert(isNormalForm());
  }

  SumPair(const Polynomial& p, const Constant& c):
    NodeWrapper(toNode(p, c))
  {
    Assert(isNormalForm());
  }

  static bool isMember(TNode n) {
    if(n.getKind() == kind::PLUS && n.getNumChildren() == 2){
      if(Constant::isMember(n[1])){
        if(Polynomial::isMember(n[0])){
          Polynomial p = Polynomial::parsePolynomial(n[0]);
          return p.isZero() || (!p.containsConstant());
        }else{
          return false;
        }
      }else{
        return false;
      }
    }else{
      return false;
    }
  }

  bool isNormalForm() const {
    return isMember(getNode());
  }

  Polynomial getPolynomial() const {
    return Polynomial::parsePolynomial(getNode()[0]);
  }

  Constant getConstant() const {
    return Constant::mkConstant((getNode())[1]);
  }

  SumPair operator+(const SumPair& other) const {
    return SumPair(getPolynomial() + other.getPolynomial(),
                   getConstant() + other.getConstant());
  }

  SumPair operator*(const Constant& c) const {
    return SumPair(getPolynomial() * c, getConstant() * c);
  }

  SumPair operator-(const SumPair& other) const {
    return (*this) + (other * Constant::mkConstant(-1));
  }

  static SumPair mkSumPair(const Polynomial& p);

  static SumPair mkSumPair(const Variable& var){
    return SumPair(Polynomial::mkPolynomial(var));
  }

  static SumPair parseSumPair(TNode n){
    return SumPair(n);
  }

  bool isIntegral() const{
    return getConstant().isIntegral() && getPolynomial().isIntegral();
  }

  bool isConstant() const {
    return getPolynomial().isZero();
  }

  bool isZero() const {
    return getConstant().isZero() && isConstant();
  }

  uint32_t size() const{
    return getPolynomial().size();
  }

  bool isNonlinear() const{
    return getPolynomial().isNonlinear();
  }

  /**
   * Returns the greatest common divisor of gcd(getPolynomial()) and getConstant().
   * The SumPair must be integral.
   */
  Integer gcd() const {
    Assert(isIntegral());
    return (getPolynomial().gcd()).gcd(getConstant().getValue().getNumerator());
  }

  uint32_t maxLength() const {
    Assert(isIntegral());
    return std::max(getPolynomial().maxLength(), getConstant().length());
  }

  static SumPair mkZero() {
    return SumPair(Polynomial::mkZero(), Constant::mkConstant(0));
  }

  static Node computeQR(const SumPair& sp, const Integer& div);

};/* class SumPair */

/* class OrderedPolynomialPair { */
/* private: */
/*   Polynomial d_first; */
/*   Polynomial d_second; */
/* public: */
/*   OrderedPolynomialPair(const Polynomial& f, const Polynomial& s) */
/*     : d_first(f), */
/*       d_second(s) */
/*   {} */

/*   /\** Returns the first part of the pair. *\/ */
/*   const Polynomial& getFirst() const { */
/*     return d_first; */
/*   } */

/*   /\** Returns the second part of the pair. *\/ */
/*   const Polynomial& getSecond() const { */
/*     return d_second; */
/*   } */

/*   OrderedPolynomialPair operator*(const Constant& c) const; */
/*   OrderedPolynomialPair operator+(const Polynomial& p) const; */

/*   /\** Returns true if both of the polynomials are constant. *\/ */
/*   bool isConstant() const; */

/*   /\** */
/*    * Evaluates an isConstant() ordered pair as if */
/*    *   (k getFirst() getRight()) */
/*    *\/ */
/*   bool evaluateConstant(Kind k) const; */

/*   /\** */
/*    * Returns the Least Common Multiple of the monomials */
/*    * on the lefthand side and the constant on the right. */
/*    *\/ */
/*   Integer denominatorLCM() const; */

/*   /\** Constructs a SumPair. *\/ */
/*   SumPair toSumPair() const; */


/*   OrderedPolynomialPair divideByGCD() const; */
/*   OrderedPolynomialPair multiplyConstant(const Constant& c) const; */

/*   /\** */
/*    * Returns true if all of the variables are integers, */
/*    * and the coefficients are integers. */
/*    *\/ */
/*   bool isIntegral() const; */

/*   /\** Returns true if all of the variables are integers. *\/ */
/*   bool allIntegralVariables() const { */
/*     return getFirst().allIntegralVariables() && getSecond().allIntegralVariables(); */
/*   } */
/* }; */

class Comparison : public NodeWrapper {
private:

  static Node toNode(Kind k, const Polynomial& l, const Constant& c);
  static Node toNode(Kind k, const Polynomial& l, const Polynomial& r);

  Comparison(TNode n);

  /**
   * Creates a node in normal form equivalent to (= l 0).
   * All variables in l are integral.
   */
  static Node mkIntEquality(const Polynomial& l);

  /**
   * Creates a comparison equivalent to (k l 0).
   * k is either GT or GEQ.
   * All variables in l are integral.
   */
  static Node mkIntInequality(Kind k, const Polynomial& l);

  /**
   * Creates a node equivalent to (= l 0).
   * It is not the case that all variables in l are integral.
   */
  static Node mkRatEquality(const Polynomial& l);

  /**
   * Creates a comparison equivalent to (k l 0).
   * k is either GT or GEQ.
   * It is not the case that all variables in l are integral.
   */
  static Node mkRatInequality(Kind k, const Polynomial& l);

public:

  Comparison(bool val) :
    NodeWrapper(NodeManager::currentNM()->mkConst(val))
  { }

  /**
   * Given a literal to TheoryArith return a single kind to
   * to indicate its underlying structure.
   * The function returns the following in each case:
   * - (K left right)           -> K where is either EQUAL, GT, or GEQ
   * - (CONST_BOOLEAN b)        -> CONST_BOOLEAN
   * - (NOT (EQUAL left right)) -> DISTINCT
   * - (NOT (GT left right))    -> LEQ
   * - (NOT (GEQ left right))   -> LT
   * If none of these match, it returns UNDEFINED_KIND.
   */
  static Kind comparisonKind(TNode literal);

  Kind comparisonKind() const { return comparisonKind(getNode()); }

  static Comparison mkComparison(Kind k, const Polynomial& l, const Polynomial& r);

  /** Returns true if the comparison is a boolean constant. */
  bool isBoolean() const;

  /**
   * Returns true if the comparison is either a boolean term,
   * in integer normal form or mixed normal form.
   */
  bool isNormalForm() const;

private:
  bool isNormalGT() const;
  bool isNormalGEQ() const;

  bool isNormalLT() const;
  bool isNormalLEQ() const;

  bool isNormalEquality() const;
  bool isNormalDistinct() const;
  bool isNormalEqualityOrDisequality() const;

  bool allIntegralVariables() const {
    return getLeft().allIntegralVariables() && getRight().allIntegralVariables();
  }
  bool rightIsConstant() const;

public:
  Polynomial getLeft() const;
  Polynomial getRight() const;

  /* /\** Normal form check if at least one variable is real. *\/ */
  /* bool isMixedCompareNormalForm() const; */

  /* /\** Normal form check if at least one variable is real. *\/ */
  /* bool isMixedEqualsNormalForm() const; */

  /* /\** Normal form check is all variables are integer.*\/ */
  /* bool isIntegerCompareNormalForm() const; */

  /* /\** Normal form check is all variables are integer.*\/ */
  /* bool isIntegerEqualsNormalForm() const; */


  /**
   * Returns true if all of the variables are integers, the coefficients are integers,
   * and the right hand coefficient is an integer.
   */
  bool debugIsIntegral() const;

  static Comparison parseNormalForm(TNode n);

  inline static bool isNormalAtom(TNode n){
    Comparison parse = Comparison::parseNormalForm(n);
    return parse.isNormalForm();
  }

  size_t getComplexity() const;

  SumPair toSumPair() const;

  Polynomial normalizedVariablePart() const;
  DeltaRational normalizedDeltaRational() const;

};/* class Comparison */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__NORMAL_FORM_H */
