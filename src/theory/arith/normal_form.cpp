/*********************                                                        */
/*! \file normal_form.cpp
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
#include "theory/arith/normal_form.h"

#include <list>

#include "base/output.h"
#include "theory/arith/arith_utilities.h"
#include "theory/theory.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

Constant Constant::mkConstant(const Rational& rat) {
  return Constant(mkRationalNode(rat));
}

size_t Variable::getComplexity() const{
  return 1u;
}

size_t VarList::getComplexity() const{
  if(empty()){
    return 1;
  }else if(singleton()){
    return 1;
  }else{
    return size() + 1;
  }
}

size_t Monomial::getComplexity() const{
  return getConstant().getComplexity() + getVarList().getComplexity();
}

size_t Polynomial::getComplexity() const{
  size_t cmp = 0;
  iterator i = begin(), e = end();
  for(; i != e; ++i){
    Monomial m = *i;
    cmp += m.getComplexity();
  }
  return cmp;
}

size_t Constant::getComplexity() const{
  return getValue().complexity();
}

bool Variable::isLeafMember(Node n){
  return (!isRelationOperator(n.getKind())) &&
    (Theory::isLeafOf(n, theory::THEORY_ARITH));
}

VarList::VarList(Node n)
  : NodeWrapper(n)
{
  Assert(isSorted(begin(), end()));
}

bool Variable::isDivMember(Node n){
  switch(n.getKind()){
  case kind::DIVISION:
  case kind::INTS_DIVISION:
  case kind::INTS_MODULUS:
  case kind::DIVISION_TOTAL:
  case kind::INTS_DIVISION_TOTAL:
  case kind::INTS_MODULUS_TOTAL:
    return Polynomial::isMember(n[0]) && Polynomial::isMember(n[1]);
  default:
    return false;
  }
}

bool Variable::isTranscendentalMember(Node n) {
  switch(n.getKind()){
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
  case kind::SQRT: return Polynomial::isMember(n[0]);
  case kind::PI:
    return true;
  default:
    return false;
  }
}


bool VarList::isSorted(iterator start, iterator end) {
  return std::is_sorted(start, end);
}

bool VarList::isMember(Node n) {
  if(Variable::isMember(n)) {
    return true;
  }
  if(n.getKind() == kind::NONLINEAR_MULT) {
    Node::iterator curr = n.begin(), end = n.end();
    Node prev = *curr;
    if(!Variable::isMember(prev)) return false;

    Variable::VariableNodeCmp cmp;

    while( (++curr) != end) {
      if(!Variable::isMember(*curr)) return false;
      // prev <= curr : accept
      // !(prev <= curr) : reject
      // !(!(prev > curr)) : reject
      // curr < prev : reject
      if((cmp(*curr, prev))) return false;
      prev = *curr;
    }
    return true;
  } else {
    return false;
  }
}

int VarList::cmp(const VarList& vl) const {
  int dif = this->size() - vl.size();
  if (dif == 0) {
    if(this->getNode() == vl.getNode()) {
      return 0;
    }

    Assert(!empty());
    Assert(!vl.empty());
    if(this->size() == 1){
      return Variable::VariableNodeCmp::cmp(this->getNode(), vl.getNode());
    }


    internal_iterator ii=this->internalBegin(), ie=this->internalEnd();
    internal_iterator ci=vl.internalBegin(), ce=vl.internalEnd();
    for(; ii != ie; ++ii, ++ci){
      Node vi = *ii;
      Node vc = *ci;
      int tmp = Variable::VariableNodeCmp::cmp(vi, vc);
      if(tmp != 0){
        return tmp;
      }
    }
    Unreachable();
  } else if(dif < 0) {
    return -1;
  } else {
    return 1;
  }
}

VarList VarList::parseVarList(Node n) {
  return VarList(n);
  // if(Variable::isMember(n)) {
  //   return VarList(Variable(n));
  // } else {
  //   Assert(n.getKind() == kind::MULT);
  //   for(Node::iterator i=n.begin(), end = n.end(); i!=end; ++i) {
  //     Assert(Variable::isMember(*i));
  //   }
  //   return VarList(n);
  // }
}

VarList VarList::operator*(const VarList& other) const {
  if(this->empty()) {
    return other;
  } else if(other.empty()) {
    return *this;
  } else {
    vector<Node> result;

    internal_iterator
      thisBegin = this->internalBegin(),
      thisEnd = this->internalEnd(),
      otherBegin = other.internalBegin(),
      otherEnd = other.internalEnd();

    Variable::VariableNodeCmp cmp;
    std::merge(thisBegin, thisEnd, otherBegin, otherEnd, std::back_inserter(result), cmp);

    Assert(result.size() >= 2);
    Node mult = NodeManager::currentNM()->mkNode(kind::NONLINEAR_MULT, result);
    return VarList::parseVarList(mult);
  }
}

bool Monomial::isMember(TNode n){
  if(n.getKind() == kind::CONST_RATIONAL) {
    return true;
  } else if(multStructured(n)) {
    return VarList::isMember(n[1]);
  } else {
    return VarList::isMember(n);
  }
}

Monomial Monomial::mkMonomial(const Constant& c, const VarList& vl) {
  if(c.isZero() || vl.empty() ) {
    return Monomial(c);
  } else if(c.isOne()) {
    return Monomial(vl);
  } else {
    return Monomial(c, vl);
  }
}

Monomial Monomial::mkMonomial(const VarList& vl) {
  // acts like Monomial::mkMonomial( 1, vl)
  if( vl.empty() ) {
    return Monomial::mkOne();
  } else if(true){
    return Monomial(vl);
  }
}

Monomial Monomial::parseMonomial(Node n) {
  if(n.getKind() == kind::CONST_RATIONAL) {
    return Monomial(Constant(n));
  } else if(multStructured(n)) {
    return Monomial::mkMonomial(Constant(n[0]),VarList::parseVarList(n[1]));
  } else {
    return Monomial(VarList::parseVarList(n));
  }
}
Monomial Monomial::operator*(const Rational& q) const {
  if(q.isZero()){
    return mkZero();
  }else{
    Constant newConstant = this->getConstant() * q;
    return Monomial::mkMonomial(newConstant, getVarList());
  }
}

Monomial Monomial::operator*(const Constant& c) const {
  return (*this) * c.getValue();
  // if(c.isZero()){
  //   return mkZero();
  // }else{
  //   Constant newConstant = this->getConstant() * c;
  //   return Monomial::mkMonomial(newConstant, getVarList());
  // }
}

Monomial Monomial::operator*(const Monomial& mono) const {
  Constant newConstant = this->getConstant() * mono.getConstant();
  VarList newVL = this->getVarList() * mono.getVarList();

  return Monomial::mkMonomial(newConstant, newVL);
}

// vector<Monomial> Monomial::sumLikeTerms(const std::vector<Monomial> & monos) {
//   Assert(isSorted(monos));
//   vector<Monomial> outMonomials;
//   typedef vector<Monomial>::const_iterator iterator;
//   for(iterator rangeIter = monos.begin(), end=monos.end(); rangeIter != end;) {
//     Rational constant = (*rangeIter).getConstant().getValue();
//     VarList varList  = (*rangeIter).getVarList();
//     ++rangeIter;
//     while(rangeIter != end && varList == (*rangeIter).getVarList()) {
//       constant += (*rangeIter).getConstant().getValue();
//       ++rangeIter;
//     }
//     if(constant != 0) {
//       Constant asConstant = Constant::mkConstant(constant);
//       Monomial nonZero = Monomial::mkMonomial(asConstant, varList);
//       outMonomials.push_back(nonZero);
//     }
//   }

//   Assert(isStrictlySorted(outMonomials));
//   return outMonomials;
// }

void Monomial::sort(std::vector<Monomial>& m){
  if(!isSorted(m)){
    std::sort(m.begin(), m.end());
  }
}

void Monomial::combineAdjacentMonomials(std::vector<Monomial>& monos) {
  Assert(isSorted(monos));
  size_t writePos, readPos, N;
  for(writePos = 0, readPos = 0, N = monos.size(); readPos < N;){
    Monomial& atRead = monos[readPos];
    const VarList& varList  = atRead.getVarList();

    size_t rangeEnd = readPos+1;
    for(; rangeEnd < N; rangeEnd++){
      if(!(varList == monos[rangeEnd].getVarList())){ break; }
    }
    // monos[i] for i in [readPos, rangeEnd) has the same var list
    if(readPos+1 == rangeEnd){ // no addition needed
      if(!atRead.getConstant().isZero()){
        Monomial cpy = atRead; // being paranoid here
        monos[writePos] = cpy;
        writePos++;
      }
    }else{
      Rational constant(monos[readPos].getConstant().getValue());
      for(size_t i=readPos+1; i < rangeEnd; ++i){
        constant += monos[i].getConstant().getValue();
      }
      if(!constant.isZero()){
        Constant asConstant = Constant::mkConstant(constant);
        Monomial nonZero = Monomial::mkMonomial(asConstant, varList);
        monos[writePos] = nonZero;
        writePos++;
      }
    }
    Assert(rangeEnd>readPos);
    readPos = rangeEnd;
  }
  if(writePos > 0 ){
    Monomial cp = monos[0];
    Assert(writePos <= N);
    monos.resize(writePos, cp);
  }else{
    monos.clear();
  }
  Assert(isStrictlySorted(monos));
}

void Monomial::print() const {
  Debug("normal-form") <<  getNode() << std::endl;
}

void Monomial::printList(const std::vector<Monomial>& list) {
  for(vector<Monomial>::const_iterator i = list.begin(), end = list.end(); i != end; ++i) {
    const Monomial& m =*i;
    m.print();
  }
}
Polynomial Polynomial::operator+(const Polynomial& vl) const {

  std::vector<Monomial> sortedMonos;
  std::merge(begin(), end(), vl.begin(), vl.end(), std::back_inserter(sortedMonos));

  Monomial::combineAdjacentMonomials(sortedMonos);
  //std::vector<Monomial> combined = Monomial::sumLikeTerms(sortedMonos);

  Polynomial result = mkPolynomial(sortedMonos);
  return result;
}

Polynomial Polynomial::exactDivide(const Integer& z) const {
  Assert(isIntegral());
  if(z.isOne()){
    return (*this);
  }else {
    Constant invz = Constant::mkConstant(Rational(1,z));
    Polynomial prod = (*this) * Monomial::mkMonomial(invz);
    Assert(prod.isIntegral());
    return prod;
  }
}

Polynomial Polynomial::sumPolynomials(const std::vector<Polynomial>& ps){
  if(ps.empty()){
    return mkZero();
  }else if(ps.size() <= 4){
    // if there are few enough polynomials just add them
    Polynomial p = ps[0];
    for(size_t i = 1; i < ps.size(); ++i){
      p = p + ps[i];
    }
    return p;
  }else{
    // general case
    std::map<Node, Rational> coeffs;
    for(size_t i = 0, N = ps.size(); i<N; ++i){
      const Polynomial& p = ps[i];
      for(iterator pi = p.begin(), pend = p.end(); pi != pend; ++pi) {
        Monomial m = *pi;
        coeffs[m.getVarList().getNode()] += m.getConstant().getValue();
      }
    }
    std::vector<Monomial> monos;
    std::map<Node, Rational>::const_iterator ci = coeffs.begin(), cend = coeffs.end();
    for(; ci != cend; ++ci){
      if(!(*ci).second.isZero()){
        Constant c = Constant::mkConstant((*ci).second);
        Node n = (*ci).first;
        VarList vl = VarList::parseVarList(n);
        monos.push_back(Monomial::mkMonomial(c, vl));
      }
    }
    Monomial::sort(monos);
    Monomial::combineAdjacentMonomials(monos);

    Polynomial result = mkPolynomial(monos);
    return result;
  }
}

Polynomial Polynomial::operator-(const Polynomial& vl) const {
  Constant negOne = Constant::mkConstant(Rational(-1));

  return *this + (vl*negOne);
}

Polynomial Polynomial::operator*(const Rational& q) const{
  if(q.isZero()){
    return Polynomial::mkZero();
  }else if(q.isOne()){
    return *this;
  }else{
    std::vector<Monomial> newMonos;
    for(iterator i = this->begin(), end = this->end(); i != end; ++i) {
      newMonos.push_back((*i)*q);
    }

    Assert(Monomial::isStrictlySorted(newMonos));
    return Polynomial::mkPolynomial(newMonos);
  }
}

Polynomial Polynomial::operator*(const Constant& c) const{
  return (*this) * c.getValue();
  // if(c.isZero()){
  //   return Polynomial::mkZero();
  // }else if(c.isOne()){
  //   return *this;
  // }else{
  //   std::vector<Monomial> newMonos;
  //   for(iterator i = this->begin(), end = this->end(); i != end; ++i) {
  //     newMonos.push_back((*i)*c);
  //   }

  //   Assert(Monomial::isStrictlySorted(newMonos));
  //   return Polynomial::mkPolynomial(newMonos);
  // }
}

Polynomial Polynomial::operator*(const Monomial& mono) const {
  if(mono.isZero()) {
    return Polynomial(mono); //Don't multiply by zero
  } else {
    std::vector<Monomial> newMonos;
    for(iterator i = this->begin(), end = this->end(); i != end; ++i) {
      newMonos.push_back(mono * (*i));
    }

    // We may need to sort newMonos.
    // Suppose this = (+ x y), mono = x, (* x y).getId() < (* x x).getId()
    // newMonos = <(* x x), (* x y)> after this loop.
    // This is not sorted according to the current VarList order.
    Monomial::sort(newMonos);
    return Polynomial::mkPolynomial(newMonos);
  }
}

Polynomial Polynomial::operator*(const Polynomial& poly) const {
  Polynomial res = Polynomial::mkZero();
  for(iterator i = this->begin(), end = this->end(); i != end; ++i) {
    Monomial curr = *i;
    Polynomial prod = poly * curr;
    Polynomial sum  = res + prod;
    res = sum;
  }
  return res;
}

Monomial Polynomial::selectAbsMinimum() const {
  iterator iter = begin(), myend = end();
  Assert(iter != myend);

  Monomial min = *iter;
  ++iter;
  for(; iter != end(); ++iter){
    Monomial curr = *iter;
    if(curr.absCmp(min) < 0){
      min = curr;
    }
  }
  return min;
}

bool Polynomial::leadingCoefficientIsAbsOne() const {
  return getHead().absCoefficientIsOne();
}
bool Polynomial::leadingCoefficientIsPositive() const {
  return getHead().getConstant().isPositive();
}

bool Polynomial::denominatorLCMIsOne() const {
  return denominatorLCM().isOne();
}

bool Polynomial::numeratorGCDIsOne() const {
  return gcd().isOne();
}

Integer Polynomial::gcd() const {
  Assert(isIntegral());
  return numeratorGCD();
}

Integer Polynomial::numeratorGCD() const {
  //We'll use the standardization that gcd(0, 0) = 0
  //So that the gcd of the zero polynomial is gcd{0} = 0
  iterator i=begin(), e=end();
  Assert(i!=e);

  Integer d = (*i).getConstant().getValue().getNumerator().abs();
  if(d.isOne()){
    return d;
  }
  ++i;
  for(; i!=e; ++i){
    Integer c = (*i).getConstant().getValue().getNumerator();
    d = d.gcd(c);
    if(d.isOne()){
      return d;
    }
  }
  return d;
}

Integer Polynomial::denominatorLCM() const {
  Integer tmp(1);
  for (iterator i = begin(), e = end(); i != e; ++i) {
    const Integer denominator = (*i).getConstant().getValue().getDenominator();
    tmp = tmp.lcm(denominator);
  }
  return tmp;
}

Constant Polynomial::getCoefficient(const VarList& vl) const{
  //TODO improve to binary search...
  for(iterator iter=begin(), myend=end(); iter != myend; ++iter){
    Monomial m = *iter;
    VarList curr = m.getVarList();
    if(curr == vl){
      return m.getConstant();
    }
  }
  return Constant::mkConstant(0);
}

Node Polynomial::computeQR(const Polynomial& p, const Integer& div){
  Assert(p.isIntegral());
  std::vector<Monomial> q_vec, r_vec;
  Integer tmp_q, tmp_r;
  for(iterator iter = p.begin(), pend = p.end(); iter != pend; ++iter){
    Monomial curr = *iter;
    VarList vl = curr.getVarList();
    Constant c = curr.getConstant();

    const Integer& a = c.getValue().getNumerator();
    Integer::floorQR(tmp_q, tmp_r, a, div);
    Constant q=Constant::mkConstant(tmp_q);
    Constant r=Constant::mkConstant(tmp_r);
    if(!q.isZero()){
      q_vec.push_back(Monomial::mkMonomial(q, vl));
    }
    if(!r.isZero()){
      r_vec.push_back(Monomial::mkMonomial(r, vl));
    }
  }

  Polynomial p_q = Polynomial::mkPolynomial(q_vec);
  Polynomial p_r = Polynomial::mkPolynomial(r_vec);

  return NodeManager::currentNM()->mkNode(kind::PLUS, p_q.getNode(), p_r.getNode());
}


Monomial Polynomial::minimumVariableMonomial() const{
  Assert(!isConstant());
  if(singleton()){
    return getHead();
  }else{
    iterator i = begin();
    Monomial first = *i;
    if( first.isConstant() ){
      ++i;
      Assert(i != end());
      return *i;
    }else{
      return first;
    }
  }
}

bool Polynomial::variableMonomialAreStrictlyGreater(const Monomial& m) const{
  if(isConstant()){
    return true;
  }else{
    Monomial minimum = minimumVariableMonomial();
    Debug("nf::tmp") << "minimum " << minimum.getNode() << endl;
    Debug("nf::tmp") << "m " << m.getNode() << endl;
    return m < minimum;
  }
}

bool Polynomial::isMember(TNode n) {
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

Node SumPair::computeQR(const SumPair& sp, const Integer& div){
  Assert(sp.isIntegral());

  const Integer& constant = sp.getConstant().getValue().getNumerator();

  Integer constant_q, constant_r;
  Integer::floorQR(constant_q, constant_r, constant, div);

  Node p_qr = Polynomial::computeQR(sp.getPolynomial(), div);
  Assert(p_qr.getKind() == kind::PLUS);
  Assert(p_qr.getNumChildren() == 2);

  Polynomial p_q = Polynomial::parsePolynomial(p_qr[0]);
  Polynomial p_r = Polynomial::parsePolynomial(p_qr[1]);

  SumPair sp_q(p_q, Constant::mkConstant(constant_q));
  SumPair sp_r(p_r, Constant::mkConstant(constant_r));

  return NodeManager::currentNM()->mkNode(kind::PLUS, sp_q.getNode(), sp_r.getNode());
}

SumPair SumPair::mkSumPair(const Polynomial& p){
  if(p.isConstant()){
    Constant leadingConstant = p.getHead().getConstant();
    return SumPair(Polynomial::mkZero(), leadingConstant);
  }else if(p.containsConstant()){
    Assert(!p.singleton());
    return SumPair(p.getTail(), p.getHead().getConstant());
  }else{
    return SumPair(p, Constant::mkZero());
  }
}

Comparison::Comparison(TNode n)
  : NodeWrapper(n)
{
  Assert(isNormalForm());
}



SumPair Comparison::toSumPair() const {
  Kind cmpKind = comparisonKind();
  switch(cmpKind){
  case kind::LT:
  case kind::LEQ:
  case kind::GT:
  case kind::GEQ:
    {
      TNode lit = getNode();
      TNode atom = (cmpKind == kind::LT || cmpKind == kind::LEQ) ? lit[0] : lit;
      Polynomial p = Polynomial::parsePolynomial(atom[0]);
      Constant c = Constant::mkConstant(atom[1]);
      if(p.leadingCoefficientIsPositive()){
        return SumPair(p, -c);
      }else{
        return SumPair(-p, c);
      }
    }
  case kind::EQUAL:
  case kind::DISTINCT:
    {
      Polynomial left = getLeft();
      Polynomial right = getRight();
      Debug("nf::tmp") << "left: " << left.getNode() << endl;
      Debug("nf::tmp") << "right: " << right.getNode() << endl;
      if(right.isConstant()){
        return SumPair(left, -right.getHead().getConstant());
      }else if(right.containsConstant()){
        Assert(!right.singleton());

        Polynomial noConstant = right.getTail();
        return SumPair(left - noConstant, -right.getHead().getConstant());
      }else{
        return SumPair(left - right, Constant::mkZero());
      }
    }
  default:
    Unhandled(cmpKind);
  }
}

Polynomial Comparison::normalizedVariablePart() const {
  Kind cmpKind = comparisonKind();
  switch(cmpKind){
  case kind::LT:
  case kind::LEQ:
  case kind::GT:
  case kind::GEQ:
    {
      TNode lit = getNode();
      TNode atom = (cmpKind == kind::LT || cmpKind == kind::LEQ) ? lit[0] : lit;
      Polynomial p = Polynomial::parsePolynomial(atom[0]);
      if(p.leadingCoefficientIsPositive()){
        return p;
      }else{
        return -p;
      }
    }
  case kind::EQUAL:
  case kind::DISTINCT:
    {
      Polynomial left = getLeft();
      Polynomial right = getRight();
      if(right.isConstant()){
        return left;
      }else{
        Polynomial noConstant = right.containsConstant() ? right.getTail() : right;
        Polynomial diff = left - noConstant;
        if(diff.leadingCoefficientIsPositive()){
          return diff;
        }else{
          return -diff;
        }
      }
    }
  default:
    Unhandled(cmpKind);
  }
}

DeltaRational Comparison::normalizedDeltaRational() const {
  Kind cmpKind = comparisonKind();
  int delta = deltaCoeff(cmpKind);
  switch(cmpKind){
  case kind::LT:
  case kind::LEQ:
  case kind::GT:
  case kind::GEQ:
    {
      Node lit = getNode();
      Node atom = (cmpKind == kind::LT || cmpKind == kind::LEQ) ? lit[0] : lit;
      Polynomial left = Polynomial::parsePolynomial(atom[0]);
      const Rational& q = atom[1].getConst<Rational>();
      if(left.leadingCoefficientIsPositive()){
        return DeltaRational(q, delta);
      }else{
        return DeltaRational(-q, -delta);
      }
    }
  case kind::EQUAL:
  case kind::DISTINCT:
    {
      Polynomial right = getRight();
      Monomial firstRight = right.getHead();
      if(firstRight.isConstant()){
        DeltaRational c = DeltaRational(firstRight.getConstant().getValue(), 0);
        Polynomial left = getLeft();
        if(!left.allIntegralVariables()){
          return c;
          //this is a qpolynomial and the sign of the leading
          //coefficient will not change after the diff below
        } else{
          // the polynomial may be a z polynomial in which case
          // taking the diff is the simplest and obviously correct means
          Polynomial diff = right.singleton() ? left : left - right.getTail();
          if(diff.leadingCoefficientIsPositive()){
            return c;
          }else{
            return -c;
          }
        }
      }else{ // The constant is 0 sign cannot change
        return DeltaRational(0, 0);
      }
    }
  default:
    Unhandled(cmpKind);
  }
}

Comparison Comparison::parseNormalForm(TNode n) {
  Debug("polynomial") << "Comparison::parseNormalForm(" << n << ")";
  Comparison result(n);
  Assert(result.isNormalForm());
  return result;
}

Node Comparison::toNode(Kind k, const Polynomial& l, const Constant& r) {
  Assert(isRelationOperator(k));
  switch(k) {
  case kind::GEQ:
  case kind::GT:
    return NodeManager::currentNM()->mkNode(k, l.getNode(), r.getNode());
  default:
    Unhandled(k);
  }
}

Node Comparison::toNode(Kind k, const Polynomial& l, const Polynomial& r) {
  Assert(isRelationOperator(k));
  switch(k) {
  case kind::GEQ:
  case kind::EQUAL:
  case kind::GT:
    return NodeManager::currentNM()->mkNode(k, l.getNode(), r.getNode());
  case kind::LEQ:
    return toNode(kind::GEQ, r, l).notNode();
  case kind::LT:
    return toNode(kind::GT, r, l).notNode();
  case kind::DISTINCT:
    return toNode(kind::EQUAL, r, l).notNode();
  default:
    Unreachable();
  }
}

bool Comparison::rightIsConstant() const {
  if(getNode().getKind() == kind::NOT){
    return getNode()[0][1].getKind() == kind::CONST_RATIONAL;
  }else{
    return getNode()[1].getKind() == kind::CONST_RATIONAL;
  }
}

size_t Comparison::getComplexity() const{
  switch(comparisonKind()){
  case kind::CONST_BOOLEAN: return 1;
  case kind::LT:
  case kind::LEQ:
  case kind::DISTINCT:
  case kind::EQUAL:
  case kind::GT:
  case kind::GEQ:
    return getLeft().getComplexity() +  getRight().getComplexity();
  default:
    Unhandled(comparisonKind());
    return -1;
  }
}

Polynomial Comparison::getLeft() const {
  TNode left;
  Kind k = comparisonKind();
  switch(k){
  case kind::LT:
  case kind::LEQ:
  case kind::DISTINCT:
    left = getNode()[0][0];
    break;
  case kind::EQUAL:
  case kind::GT:
  case kind::GEQ:
    left = getNode()[0];
    break;
  default:
    Unhandled(k);
  }
  return Polynomial::parsePolynomial(left);
}

Polynomial Comparison::getRight() const {
  TNode right;
  Kind k = comparisonKind();
  switch(k){
  case kind::LT:
  case kind::LEQ:
  case kind::DISTINCT:
    right = getNode()[0][1];
    break;
  case kind::EQUAL:
  case kind::GT:
  case kind::GEQ:
    right = getNode()[1];
    break;
  default:
    Unhandled(k);
  }
  return Polynomial::parsePolynomial(right);
}

// Polynomial Comparison::getLeft() const {
//   Node n = getNode();
//   Node left = (n.getKind() == kind::NOT ? n[0]: n)[0];
//   return Polynomial::parsePolynomial(left);
// }

// Polynomial Comparison::getRight() const {
//   Node n = getNode();
//   Node right = (n.getKind() == kind::NOT ? n[0]: n)[1];
//   return Polynomial::parsePolynomial(right);
// }

bool Comparison::isNormalForm() const {
  Node n = getNode();
  Kind cmpKind = comparisonKind(n);
  Debug("nf::tmp") << "isNormalForm " << n << " " << cmpKind << endl;
  switch(cmpKind){
  case kind::CONST_BOOLEAN:
    return true;
  case kind::GT:
    return isNormalGT();
  case kind::GEQ:
    return isNormalGEQ();
  case kind::EQUAL:
    return isNormalEquality();
  case kind::LT:
    return isNormalLT();
  case kind::LEQ:
    return isNormalLEQ();
  case kind::DISTINCT:
    return isNormalDistinct();
  default:
    return false;
  }
}

/** This must be (> qpolynomial constant) */
bool Comparison::isNormalGT() const {
  Node n = getNode();
  Assert(n.getKind() == kind::GT);
  if(!rightIsConstant()){
    return false;
  }else{
    Polynomial left = getLeft();
    if(left.containsConstant()){
      return false;
    }else if(!left.leadingCoefficientIsAbsOne()){
      return false;
    }else{
      return !left.isIntegral();
    }
  }
}

/** This must be (not (> qpolynomial constant)) */
bool Comparison::isNormalLEQ() const {
  Node n = getNode();
  Debug("nf::tmp") << "isNormalLEQ " << n << endl;
  Assert(n.getKind() == kind::NOT);
  Assert(n[0].getKind() == kind::GT);
  if(!rightIsConstant()){
    return false;
  }else{
    Polynomial left = getLeft();
    if(left.containsConstant()){
      return false;
    }else if(!left.leadingCoefficientIsAbsOne()){
      return false;
    }else{
      return !left.isIntegral();
    }
  }
}


/** This must be (>= qpolynomial constant) or  (>= zpolynomial constant) */
bool Comparison::isNormalGEQ() const {
  Node n = getNode();
  Assert(n.getKind() == kind::GEQ);

  Debug("nf::tmp") << "isNormalGEQ " << n << " " << rightIsConstant() << endl;

  if(!rightIsConstant()){
    return false;
  }else{
    Polynomial left = getLeft();
    if(left.containsConstant()){
      return false;
    }else{
      if(left.isIntegral()){
        return left.signNormalizedReducedSum();
      }else{
        return left.leadingCoefficientIsAbsOne();
      }
    }
  }
}

/** This must be (not (>= qpolynomial constant)) or (not (>= zpolynomial constant)) */
bool Comparison::isNormalLT() const {
  Node n = getNode();
  Assert(n.getKind() == kind::NOT);
  Assert(n[0].getKind() == kind::GEQ);

  if(!rightIsConstant()){
    return false;
  }else{
    Polynomial left = getLeft();
    if(left.containsConstant()){
      return false;
    }else{
      if(left.isIntegral()){
        return left.signNormalizedReducedSum();
      }else{
        return left.leadingCoefficientIsAbsOne();
      }
    }
  }
}


bool Comparison::isNormalEqualityOrDisequality() const {
  Polynomial pleft = getLeft();

  if(pleft.numMonomials() == 1){
    Monomial mleft = pleft.getHead();
    if(mleft.isConstant()){
      return false;
    }else{
      Polynomial pright = getRight();
      if(allIntegralVariables()){
        const Rational& lcoeff = mleft.getConstant().getValue();
        if(pright.isConstant()){
          return pright.isIntegral() && lcoeff.isOne();
        }
        Polynomial varRight = pright.containsConstant() ? pright.getTail() : pright;
        if(lcoeff.sgn() <= 0){
          return false;
        }else{
          Integer lcm = lcoeff.getDenominator().lcm(varRight.denominatorLCM());
          Integer g = lcoeff.getNumerator().gcd(varRight.numeratorGCD());
          Debug("nf::tmp") << lcm << " " << g << endl;
          if(!lcm.isOne()){
            return false;
          }else if(!g.isOne()){
            return false;
          }else{
            Monomial absMinRight = varRight.selectAbsMinimum();
            Debug("nf::tmp") << mleft.getNode() << " " << absMinRight.getNode() << endl;
            if( mleft.absCmp(absMinRight) < 0){
              return true;
            }else{
              return (!(absMinRight.absCmp(mleft)< 0)) && mleft < absMinRight;
            }
          }
        }
      }else{
        if(mleft.coefficientIsOne()){
          Debug("nf::tmp")
            << "dfklj " << mleft.getNode() << endl
            << pright.getNode() << endl
            << pright.variableMonomialAreStrictlyGreater(mleft)
            << endl;
          return pright.variableMonomialAreStrictlyGreater(mleft);
        }else{
          return false;
        }
      }
    }
  }else{
    return false;
  }
}

/** This must be (= qvarlist qpolynomial) or (= zmonomial zpolynomial)*/
bool Comparison::isNormalEquality() const {
  Assert(getNode().getKind() == kind::EQUAL);
  return Theory::theoryOf(getNode()[0].getType()) == THEORY_ARITH &&
         isNormalEqualityOrDisequality();
}

/**
 * This must be (not (= qvarlist qpolynomial)) or
 * (not (= zmonomial zpolynomial)).
 */
bool Comparison::isNormalDistinct() const {
  Assert(getNode().getKind() == kind::NOT);
  Assert(getNode()[0].getKind() == kind::EQUAL);

  return Theory::theoryOf(getNode()[0][0].getType()) == THEORY_ARITH &&
         isNormalEqualityOrDisequality();
}

Node Comparison::mkRatEquality(const Polynomial& p){
  Assert(!p.isConstant());
  Assert(!p.allIntegralVariables());

  Monomial minimalVList = p.minimumVariableMonomial();
  Constant coeffInv = -(minimalVList.getConstant().inverse());

  Polynomial newRight = (p - minimalVList) * coeffInv;
  Polynomial newLeft(Monomial::mkMonomial(minimalVList.getVarList()));

  return toNode(kind::EQUAL, newLeft, newRight);
}

Node Comparison::mkRatInequality(Kind k, const Polynomial& p){
  Assert(k == kind::GEQ || k == kind::GT);
  Assert(!p.isConstant());
  Assert(!p.allIntegralVariables());

  SumPair sp = SumPair::mkSumPair(p);
  Polynomial left = sp.getPolynomial();
  Constant right = - sp.getConstant();

  Monomial minimalVList = left.getHead();
  Assert(!minimalVList.isConstant());

  Constant coeffInv = minimalVList.getConstant().inverse().abs();
  Polynomial newLeft = left * coeffInv;
  Constant newRight = right * (coeffInv);

  return toNode(k, newLeft, newRight);
}

Node Comparison::mkIntInequality(Kind k, const Polynomial& p){
  Assert(kind::GT == k || kind::GEQ == k);
  Assert(!p.isConstant());
  Assert(p.allIntegralVariables());

  SumPair sp = SumPair::mkSumPair(p);
  Polynomial left = sp.getPolynomial();
  Rational right = - (sp.getConstant().getValue());


  Monomial m = left.getHead();
  Assert(!m.isConstant());

  Integer lcm = left.denominatorLCM();
  Integer g = left.numeratorGCD();
  Rational mult(lcm,g);

  Polynomial newLeft = left * mult;
  Rational rightMult = right * mult;

  bool negateResult = false;
  if(!newLeft.leadingCoefficientIsPositive()){
    // multiply by -1
    // a: left >= right or b: left > right
    // becomes
    // a: -left <= -right or b: -left < -right
    // a: not (-left > -right) or b: (not -left >= -right)
    newLeft = -newLeft;
    rightMult = -rightMult;
    k = (kind::GT == k) ? kind::GEQ : kind::GT;
    negateResult = true;
    // the later stages handle:
    // a: not (-left >= -right + 1) or b: (not -left >= -right)
  }

  Node result = Node::null();
  if(rightMult.isIntegral()){
    if(k == kind::GT){
      // (> p z)
      // (>= p (+ z 1))
      Constant rightMultPlusOne = Constant::mkConstant(rightMult + 1);
      result = toNode(kind::GEQ, newLeft, rightMultPlusOne);
    }else{
      Constant newRight = Constant::mkConstant(rightMult);
      result = toNode(kind::GEQ, newLeft, newRight);
    }
  }else{
    //(>= l (/ n d))
    //(>= l (ceil (/ n d)))
    //This also hold for GT as (ceil (/ n d)) > (/ n d)
    Integer ceilr = rightMult.ceiling();
    Constant ceilRight = Constant::mkConstant(ceilr);
    result = toNode(kind::GEQ, newLeft, ceilRight);
  }
  Assert(!result.isNull());
  if(negateResult){
    return result.notNode();
  }else{
    return result;
  }
}

Node Comparison::mkIntEquality(const Polynomial& p){
  Assert(!p.isConstant());
  Assert(p.allIntegralVariables());

  SumPair sp = SumPair::mkSumPair(p);
  Polynomial varPart = sp.getPolynomial();
  Constant constPart = sp.getConstant();

  Integer lcm = varPart.denominatorLCM();
  Integer g = varPart.numeratorGCD();
  Constant mult = Constant::mkConstant(Rational(lcm,g));

  Constant constMult = constPart * mult;

  if(constMult.isIntegral()){
    Polynomial varPartMult = varPart * mult;

    Monomial m = varPartMult.selectAbsMinimum();
    bool mIsPositive =  m.getConstant().isPositive();

    Polynomial noM = (varPartMult + (- m)) + Polynomial::mkPolynomial(constMult);

    // m + noM = 0
    Polynomial newRight = mIsPositive ? -noM : noM;
    Polynomial newLeft  = mIsPositive ? m  : -m;

    Assert(newRight.isIntegral());
    return toNode(kind::EQUAL, newLeft, newRight);
  }else{
    return mkBoolNode(false);
  }
}

Comparison Comparison::mkComparison(Kind k, const Polynomial& l, const Polynomial& r){

  //Make this special case fast for sharing!
  if((k == kind::EQUAL || k == kind::DISTINCT) && l.isVarList() && r.isVarList()){
    VarList vLeft = l.asVarList();
    VarList vRight = r.asVarList();

    if(vLeft == vRight){
      // return true for equalities and false for disequalities
      return Comparison(k == kind::EQUAL);
    }else{
      Node eqNode = vLeft < vRight ? toNode( kind::EQUAL, l, r) : toNode( kind::EQUAL, r, l);
      Node forK = (k == kind::DISTINCT) ? eqNode.notNode() : eqNode;
      return Comparison(forK);
    }
  }

  //General case
  Polynomial diff = l - r;
  if(diff.isConstant()){
    bool res = evaluateConstantPredicate(k, diff.asConstant(), Rational(0));
    return Comparison(res);
  }else{
    Node result = Node::null();
    bool isInteger = diff.allIntegralVariables();
    switch(k){
    case kind::EQUAL:
      result = isInteger ? mkIntEquality(diff) : mkRatEquality(diff);
      break;
    case kind::DISTINCT:
      {
        Node eq = isInteger ? mkIntEquality(diff) : mkRatEquality(diff);
        result = eq.notNode();
      }
      break;
    case kind::LEQ:
    case kind::LT:
      {
        Polynomial neg = - diff;
        Kind negKind = (k == kind::LEQ ? kind::GEQ : kind::GT);
        result = isInteger ?
          mkIntInequality(negKind, neg) : mkRatInequality(negKind, neg);
      }
      break;
    case kind::GEQ:
    case kind::GT:
      result = isInteger ?
        mkIntInequality(k, diff) : mkRatInequality(k, diff);
      break;
    default:
      Unhandled(k);
    }
    Assert(!result.isNull());
    if(result.getKind() == kind::NOT && result[0].getKind() == kind::CONST_BOOLEAN){
      return Comparison(!(result[0].getConst<bool>()));
    }else{
      Comparison cmp(result);
      Assert(cmp.isNormalForm());
      return cmp;
    }
  }
}

bool Comparison::isBoolean() const {
  return getNode().getKind() == kind::CONST_BOOLEAN;
}


bool Comparison::debugIsIntegral() const{
  return getLeft().isIntegral() && getRight().isIntegral();
}

Kind Comparison::comparisonKind(TNode literal){
  switch(literal.getKind()){
  case kind::CONST_BOOLEAN:
  case kind::GT:
  case kind::GEQ:
  case kind::EQUAL:
    return literal.getKind();
  case  kind::NOT:
    {
      TNode negatedAtom = literal[0];
      switch(negatedAtom.getKind()){
      case kind::GT: //(not (GT x c)) <=> (LEQ x c)
        return kind::LEQ;
      case kind::GEQ: //(not (GEQ x c)) <=> (LT x c)
        return kind::LT;
      case kind::EQUAL:
        return kind::DISTINCT;
      default:
        return  kind::UNDEFINED_KIND;
      }
    }
  default:
    return kind::UNDEFINED_KIND;
  }
}


Node Polynomial::makeAbsCondition(Variable v, Polynomial p){
  Polynomial zerop = Polynomial::mkZero();

  Polynomial varp = Polynomial::mkPolynomial(v);
  Comparison pLeq0 = Comparison::mkComparison(kind::LEQ, p, zerop);
  Comparison negP = Comparison::mkComparison(kind::EQUAL, varp, -p);
  Comparison posP = Comparison::mkComparison(kind::EQUAL, varp, p);

  Node absCnd = (pLeq0.getNode()).iteNode(negP.getNode(), posP.getNode());
  return absCnd;
}

bool Polynomial::isNonlinear() const {

  for(iterator i=begin(), iend =end(); i != iend; ++i){
    Monomial m = *i;
    if(m.isNonlinear()){
      return true;
    }
  }
  return false;
}

} //namespace arith
} //namespace theory
} //namespace CVC4
