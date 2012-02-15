/*********************                                                        */
/*! \file normal_form.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__NORMAL_FORM_H
#define __CVC4__THEORY__ARITH__NORMAL_FORM_H

#include "expr/node.h"
#include "expr/node_self_iterator.h"
#include "util/rational.h"
#include "theory/theory.h"
#include "theory/arith/arith_utilities.h"

#include <list>
#include <algorithm>
#include <ext/algorithm>

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
 *     n.getMetaKind() == metakind::VARIABLE
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
 * rational_restricted_cmp := (|><| qpolynomial constant)
 *   where
 *     |><| is GEQ, EQ, or EQ
 *     not (exists constantMonomial (monomialList qpolynomial))
 *     (exists realMonomial (monomialList qpolynomial))
 *     monomialCoefficient (head (monomialList qpolynomial)) == 1
 *
 * integer_restricted_cmp := (|><| zpolynomial constant)
 *   where
 *     |><| is GEQ, EQ, or EQ
 *     not (exists constantMonomial (monomialList zpolynomial))
 *     (forall integerMonomial (monomialList qpolynomial))
 *     the denominator of all coefficients and the constant is 1
 *     the gcd of all numerators of coefficients is 1
 *
 * comparison := TRUE | FALSE
 *   | rational_restricted_cmp | (not rational_restricted_cmp)
 *   | integer_restricted_cmp | (not integer_restricted_cmp)
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
    if (n.getKind() == kind::CONST_INTEGER) return false;
    if (n.getKind() == kind::CONST_RATIONAL) return false;
    if (isRelationOperator(n.getKind())) return false;
    return Theory::isLeafOf(n, theory::THEORY_ARITH);
  }

  bool isNormalForm() { return isMember(getNode()); }

  bool isIntegral() const {
    return getNode().getType().isInteger();
  }

  bool operator<(const Variable& v) const { return getNode() < v.getNode();}
  bool operator==(const Variable& v) const { return getNode() == v.getNode();}

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
    return Constant(coerceToRationalNode(n));
  }

  static Constant mkConstant(const Rational& rat) {
    return Constant(mkRationalNode(rat));
  }

  const Rational& getValue() const {
    return getNode().getConst<Rational>();
  }

  bool isIntegral() const { return getValue().isIntegral(); }

  int sgn() const { return getValue().sgn(); }

  bool isZero() const { return sgn() == 0; }
  bool isNegative() const { return sgn() < 0; }
  bool isPositive() const { return sgn() > 0; }

  bool isOne() const { return getValue() == 1; }

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


template <class GetNodeIterator, class T>
static void copy_range(GetNodeIterator begin, GetNodeIterator end, std::vector<T>& result){
  while(begin != end){
    result.push_back(*begin);
    ++begin;
  }
}

template <class GetNodeIterator, class T>
static void merge_ranges(GetNodeIterator first1,
                  GetNodeIterator last1,
                  GetNodeIterator first2,
                  GetNodeIterator last2,
                  std::vector<T>& result) {

  while(first1 != last1 && first2 != last2){
    if( (*first1) < (*first2) ){
      result.push_back(*first1);
      ++ first1;
    }else{
      result.push_back(*first2);
      ++ first2;
    }
  }
  copy_range(first1, last1, result);
  copy_range(first2, last2, result);
}

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

    return makeNode(kind::MULT, list.begin(), list.end());
  }

  VarList() : NodeWrapper(Node::null()) {}

  VarList(Node n) : NodeWrapper(n) {
    Assert(isSorted(begin(), end()));
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

public:

  class iterator {
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
    return !empty() && getNode().getKind() != kind::MULT;
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

private:
  bool isSorted(iterator start, iterator end);

};/* class VarList */


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

public:

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

  static bool isMember(TNode n);

  /** Makes a monomial with no restrictions on c and vl. */
  static Monomial mkMonomial(const Constant& c, const VarList& vl);

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

  Monomial operator*(const Monomial& mono) const;


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
    return __gnu_cxx::is_sorted(m.begin(), m.end());
  }

  static bool isStrictlySorted(const std::vector<Monomial>& m) {
    return isSorted(m) && std::adjacent_find(m.begin(),m.end()) == m.end();
  }

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

  /**
   * Given a sorted list of monomials, this function transforms this
   * into a strictly sorted list of monomials that does not contain zero.
   */
  static std::vector<Monomial> sumLikeTerms(const std::vector<Monomial>& monos);

  bool absLessThan(const Monomial& other) const{
    return getConstant().abs() < other.getConstant().abs();
  }

  uint32_t coefficientLength() const{
    return getConstant().length();
  }

  void print() const;
  static void printList(const std::vector<Monomial>& list);

};/* class Monomial */


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
  static bool isMember(TNode n) {
    if(Monomial::isMember(n)){
      return true;
    }else if(n.getKind() == kind::PLUS){
      Assert(n.getNumChildren() >= 2);
      Node::iterator currIter = n.begin(), end = n.end();
      Node prev = *currIter;
      if(!Monomial::isMember(prev)){
        return false;
      }

      Monomial mprev = Monomial::parseMonomial(prev);
      ++currIter;
      for(; currIter != end; ++currIter){
        Node curr = *currIter;
        if(!Monomial::isMember(curr)){
          return false;
        }
        Monomial mcurr = Monomial::parseMonomial(curr);
        if(!(mprev < mcurr)){
          return false;
        }
        mprev = mcurr;
      }
      return true;
    } else {
      return false;
    }
  }

  class iterator {
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

  static Polynomial mkPolynomial(const Variable& v){
    return Monomial::mkMonomial(v);
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

  Monomial getHead() const {
    return *(begin());
  }

  Polynomial getTail() const {
    Assert(! singleton());

    iterator tailStart = begin();
    ++tailStart;
    std::vector<Monomial> subrange;
    copy_range(tailStart, end(), subrange);
    return mkPolynomial(subrange);
  }

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

  /**
   * Selects a minimal monomial in the polynomial by the absolute value of
   * the coefficient.
   */
  Monomial selectAbsMinimum() const;

  /**
   * Returns the Least Common Multiple of the denominators of the coefficients
   * of the monomials.
   */
  Integer denominatorLCM() const;

  /**
   * Returns the GCD of the coefficients of the monomials.
   * Requires this to be an isIntegral() polynomial.
   */
  Integer gcd() const;

  Polynomial exactDivide(const Integer& z) const {
    Assert(isIntegral());
    Constant invz = Constant::mkConstant(Rational(1,z));
    Polynomial prod = (*this) * Monomial(invz);
    Assert(prod.isIntegral());
    return prod;
  }

  Polynomial operator+(const Polynomial& vl) const;

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

  /** Returns the coefficient assiociated with the VarList in the polynomial. */
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
};/* class Polynomial */


class Comparison : public NodeWrapper {
private:
  Kind oper;
  Polynomial left;
  Constant right;

  static Node toNode(Kind k, const Polynomial& l, const Constant& r);

  Comparison(TNode n, Kind k, const Polynomial& l, const Constant& r):
    NodeWrapper(n), oper(k), left(l), right(r)
  { }

  /**
   * Possibly simplify a comparison with a pseudoboolean-typed LHS.  k
   * is one of LT, LEQ, EQUAL, GEQ, GT, and left must be PB-typed.  If
   * possible, "left k right" is fully evaluated, "true" is returned,
   * and the result of the evaluation is returned in "result".  If no
   * evaluation is possible, false is returned and "result" is
   * untouched.
   *
   * For example, pbComparison(kind::EQUAL, "x", 0.5, result) returns
   * true, and updates "result" to false, since pseudoboolean variable
   * "x" can never equal 0.5.  pbComparison(kind::GEQ, "x", 1, result)
   * returns false, since "x" can be >= 1, but could also be less.
   */
  static bool pbComparison(Kind k, TNode left, const Rational& right, bool& result);

  Kind getKind() const { return oper; }

public:
  Comparison(bool val) :
    NodeWrapper(NodeManager::currentNM()->mkConst(val)),
    oper(kind::CONST_BOOLEAN),
    left(Polynomial::mkZero()),
    right(Constant::mkConstant(0))
  { }

  Comparison(Kind k, const Polynomial& l, const Constant& r):
    NodeWrapper(toNode(k, l, r)), oper(k), left(l), right(r)
  {
    Assert(isRelationOperator(oper));
    Assert(!left.containsConstant());
    Assert(left.getHead().getConstant().isOne());
  }

  static Comparison mkComparison(Kind k, const Polynomial& left, const Constant& right);

  /**
   * Returns the left hand side of the comparison.
   * This is a polynomial that always contains all of the variables.
   */
  const Polynomial& getLeft() const { return left; }

  /**
   * Returns the right hand constatn of the comparison.
   * If in normal form, this is the only constant term.
   */
  const Constant& getRight() const { return right; }

  /** Returns true if the comparison is a boolean constant. */
  bool isBoolean() const {
    return (oper == kind::CONST_BOOLEAN);
  }

  /** Returns true if all of the variables are integers. */
  bool allIntegralVariables() const {
    return getLeft().allIntegralVariables();
  }

  /**
   * Returns true if the comparison is either a boolean term,
   * in integer normal form or mixed normal form.
   */
  bool isNormalForm() const {
    if(isBoolean()) {
      return true;
    } else if(allIntegralVariables()) {
      return isIntegerNormalForm();
    } else{
      return isMixedNormalForm();
    }
  }

private:
  /** Normal form check if at least one variable is real. */
  bool isMixedNormalForm() const;

  /** Normal form check is all variables are real.*/
  bool isIntegerNormalForm() const;

public:
  /**
   * Returns true if the left hand side is the sum of a non-zero constant
   * and a polynomial.*/
  bool constantInLefthand() const;

  /**
   * Returns a polynomial that is equivalent to the original but does not contain
   * a constant in the top level sum on the left hand side.
   */
  Comparison cancelLefthandConstant() const;


  /** Returns true if the polynomial is a constant. */
  bool isConstant() const;

  /** Reduces a constant comparison to a boolean comaprison.*/
  Comparison evaluateConstant() const;


  /**
   * Returns true if all of the variables are integers, the coefficients are integers,
   * and the right hand coefficient is an integer.
   */
  bool isIntegral() const;

  /**
   * Returns the Least Common Multiple of the monomials
   * on the lefthand side and the constant on the right.
   */
  Integer denominatorLCM() const;

  /** Multiplies the comparison by the denominatorLCM(). */
  Comparison multiplyByDenominatorLCM() const;

  /** If the leading coefficient is negative, multiply by -1. */
  Comparison normalizeLeadingCoefficientPositive() const;

  /** Divides the Comaprison by the gcd of the lefthand.*/
  Comparison divideByLefthandGCD() const;

  /** Divides the Comparison by the leading coefficient. */
  Comparison divideByLeadingCoefficient() const;

  /**
   * If the left hand is integral and the right hand is not,
   * the comparison is tightened to the nearest integer.
   */
  Comparison tightenIntegralConstraint() const;

  Comparison addConstant(const Constant& constant) const;

  /* Multiply a non-boolean comparison by a constant term. */
  Comparison multiplyConstant(const Constant& constant) const;

  static Comparison parseNormalForm(TNode n);

  /* Returns a logically equivalent comparison in normal form. */
  static Comparison normalize(Comparison c);

  /** Makes a comparison that is in normal form. */
  static Comparison mkNormalComparison(Kind k, const Polynomial& left, const Constant& right);

  inline static bool isNormalAtom(TNode n){
    Comparison parse = Comparison::parseNormalForm(n);
    return parse.isNormalForm();
  }

};/* class Comparison */

/**
 * SumPair is a utility class that extends polynomials for use in computations.
 * A SumPair is always a combination of (+ p c) where
 *  c is a constant and p is a polynomial such that p = 0 or !p.containsConstant().
 *
 * These are a useful utility for representing the equation p = c as (+ p -c) where the pair
 * is known to implicitly be equal to 0.
 *
 * SumPairs do not have unique representations due to the potential for p = 0.
 * This makes them inappropraite for normal forms.
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


  static SumPair comparisonToSumPair(const Comparison& cmp){
    return SumPair(cmp.getLeft(), - cmp.getRight());
  }

};/* class SumPair */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__NORMAL_FORM_H */
