/******************************************************************************
 * Top contributors (to current version):
 *   Liana Hadarean, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of bitblasting functions for various operators.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BITBLAST__BITBLAST_STRATEGIES_TEMPLATE_H
#define CVC5__THEORY__BV__BITBLAST__BITBLAST_STRATEGIES_TEMPLATE_H

#include <cmath>
#include <ostream>

#include "expr/node.h"
#include "theory/bv/bitblast/bitblast_utils.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"

namespace cvc5::internal {

namespace theory {
namespace bv {

/** 
 * Default Atom Bitblasting strategies: 
 * 
 * @param node the atom to be bitblasted
 * @param bb the bitblaster
 */

template <class T>
T UndefinedAtomBBStrategy(TNode node, TBitblaster<T>* bb) {
  Trace("bitvector") << "TheoryBV::Bitblaster Undefined bitblasting strategy for kind: "
                     << node.getKind() << "\n";
  Unreachable(); 
}


template <class T>
T DefaultEqBB(TNode node, TBitblaster<T>* bb) {
  Trace("bitvector-bb") << "Bitblasting node " << node  << "\n";

  Assert(node.getKind() == kind::EQUAL);
  std::vector<T> lhs, rhs; 
  bb->bbTerm(node[0], lhs);
  bb->bbTerm(node[1], rhs);

  Assert(lhs.size() == rhs.size());

  std::vector<T> bits_eq;
  for (unsigned i = 0; i < lhs.size(); i++) {
    T bit_eq = mkIff(lhs[i], rhs[i]);
    bits_eq.push_back(bit_eq); 
  }
  T bv_eq = mkAnd(bits_eq);
  return bv_eq; 
}

template <class T>
T AdderUltBB(TNode node, TBitblaster<T>* bb) {
  Trace("bitvector-bb") << "Bitblasting node " << node  << "\n";
  Assert(node.getKind() == kind::BITVECTOR_ULT);
  std::vector<T> a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);
  Assert(a.size() == b.size());

  // a < b <=> ~ (add(a, ~b, 1).carry_out)
  std::vector<T> not_b;
  negateBits(b, not_b);
  T carry = mkTrue<T>();
  
  for (unsigned i = 0 ; i < a.size(); ++i) {
    carry = mkOr( mkAnd(a[i], not_b[i]),
                  mkAnd( mkXor(a[i], not_b[i]),
                         carry));
  }
  return mkNot(carry); 
}


template <class T>
T DefaultUltBB(TNode node, TBitblaster<T>* bb) {
  Trace("bitvector-bb") << "Bitblasting node " << node  << "\n";
  Assert(node.getKind() == kind::BITVECTOR_ULT);
  std::vector<T> a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);
  Assert(a.size() == b.size());

  // construct bitwise comparison 
  T res = uLessThanBB(a, b, false);
  return res; 
}

template <class T>
T DefaultUleBB(TNode node, TBitblaster<T>* bb){
  Trace("bitvector-bb") << "Bitblasting node " << node  << "\n";
  Assert(node.getKind() == kind::BITVECTOR_ULE);
  std::vector<T> a, b;
  
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);
  Assert(a.size() == b.size());
  // construct bitwise comparison 
  T res = uLessThanBB(a, b, true);
  return res; 
}

template <class T>
T DefaultUgtBB(TNode node, TBitblaster<T>* bb){
  Trace("bitvector-bb") << "Bitblasting node " << node  << "\n";
  // should be rewritten 
  Unimplemented(); 
}
template <class T>
T DefaultUgeBB(TNode node, TBitblaster<T>* bb){
  Trace("bitvector-bb") << "Bitblasting node " << node  << "\n";
  // should be rewritten 
  Unimplemented(); 
}

template <class T>
T DefaultSltBB(TNode node, TBitblaster<T>* bb){
  Trace("bitvector-bb") << "Bitblasting node " << node  << "\n";

  std::vector<T> a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);
  Assert(a.size() == b.size());

  T res = sLessThanBB(a, b, false); 
  return res;
}

template <class T>
T DefaultSleBB(TNode node, TBitblaster<T>* bb){
  Trace("bitvector-bb") << "Bitblasting node " << node  << "\n";

  std::vector<T> a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);
  Assert(a.size() == b.size());

  T res = sLessThanBB(a, b, true); 
  return res;
}
 
template <class T>
T DefaultSgtBB(TNode node, TBitblaster<T>* bb){
  Trace("bitvector-bb") << "Bitblasting node " << node  << "\n";
  // should be rewritten 
  Unimplemented(); 
}

template <class T>
T DefaultSgeBB(TNode node, TBitblaster<T>* bb){
  Trace("bitvector-bb") << "Bitblasting node " << node  << "\n";
  // should be rewritten 
  Unimplemented(); 
}


/// Term bitblasting strategies 

/** 
 * Default Term Bitblasting strategies
 * 
 * @param node the term to be bitblasted
 * @param bits [output parameter] bits representing the new term 
 * @param bb the bitblaster in which the clauses are added
 */
template <class T>
void UndefinedTermBBStrategy(TNode node, std::vector<T>& bits, TBitblaster<T>* bb) {
  Trace("bitvector") << "theory::bv:: Undefined bitblasting strategy for kind: "
                     << node.getKind() << "\n";
  Unreachable(); 
}

template <class T>
void DefaultVarBB (TNode node, std::vector<T>& bits, TBitblaster<T>* bb) {
  Assert(bits.size() == 0);
  bb->makeVariable(node, bits);

  if(TraceIsOn("bitvector-bb")) {
    Trace("bitvector-bb") << "theory::bv::DefaultVarBB bitblasting  " << node << "\n";
    Trace("bitvector-bb") << "                           with bits  " << toString(bits); 
  }
}

template <class T>
void DefaultConstBB (TNode node, std::vector<T>& bits, TBitblaster<T>* bb) {
  Trace("bitvector-bb") << "theory::bv::DefaultConstBB bitblasting " << node << "\n";
  Assert(node.getKind() == kind::CONST_BITVECTOR);
  Assert(bits.size() == 0);

  for (unsigned i = 0; i < utils::getSize(node); ++i) {
    Integer bit = node.getConst<BitVector>().extract(i, i).getValue();
    if(bit == Integer(0)){
      bits.push_back(mkFalse<T>());
    } else {
      Assert(bit == Integer(1));
      bits.push_back(mkTrue<T>()); 
    }
  }
  if(TraceIsOn("bitvector-bb")) {
    Trace("bitvector-bb") << "with  bits: " << toString(bits) << "\n"; 
  }
}


template <class T>
void DefaultNotBB (TNode node, std::vector<T>& bits, TBitblaster<T>* bb) {
  Trace("bitvector-bb") << "theory::bv::DefaultNotBB bitblasting " << node << "\n";
  Assert(node.getKind() == kind::BITVECTOR_NOT);
  Assert(bits.size() == 0);
  std::vector<T> bv; 
  bb->bbTerm(node[0], bv);
  negateBits(bv, bits);
}

template <class T>
void DefaultConcatBB (TNode node, std::vector<T>& bits, TBitblaster<T>* bb) {
  Trace("bitvector-bb") << "theory::bv::DefaultConcatBB bitblasting " << node << "\n";
  Assert(bits.size() == 0);

  Assert(node.getKind() == kind::BITVECTOR_CONCAT);
  for (int i = node.getNumChildren() -1 ; i >= 0; --i ) {
    TNode current = node[i];
    std::vector<T> current_bits; 
    bb->bbTerm(current, current_bits);

    for(unsigned j = 0; j < utils::getSize(current); ++j) {
      bits.push_back(current_bits[j]);
    }
  }
  Assert(bits.size() == utils::getSize(node));
  if(TraceIsOn("bitvector-bb")) {
    Trace("bitvector-bb") << "with  bits: " << toString(bits) << "\n"; 
  }
}

template <class T>
void DefaultAndBB (TNode node, std::vector<T>& bits, TBitblaster<T>* bb) {
  Trace("bitvector-bb") << "theory::bv::DefaultAndBB bitblasting " << node << "\n";

  Assert(node.getKind() == kind::BITVECTOR_AND && bits.size() == 0);

  bb->bbTerm(node[0], bits);
  std::vector<T> current;
  for(unsigned j = 1; j < node.getNumChildren(); ++j) {
    bb->bbTerm(node[j], current);
    for (unsigned i = 0; i < utils::getSize(node); ++i) {
      bits[i] = mkAnd(bits[i], current[i]);
    }
    current.clear();
  }
  Assert(bits.size() == utils::getSize(node));
}

template <class T>
void DefaultOrBB (TNode node, std::vector<T>& bits, TBitblaster<T>* bb) {
  Trace("bitvector-bb") << "theory::bv::DefaultOrBB bitblasting " << node << "\n";

  Assert(node.getKind() == kind::BITVECTOR_OR && bits.size() == 0);

  bb->bbTerm(node[0], bits);
  std::vector<T> current;
  for(unsigned j = 1; j < node.getNumChildren(); ++j) {
    bb->bbTerm(node[j], current);
    for (unsigned i = 0; i < utils::getSize(node); ++i) {
      bits[i] = mkOr(bits[i], current[i]);
    }
    current.clear();
  }
  Assert(bits.size() == utils::getSize(node));
}

template <class T>
void DefaultXorBB (TNode node, std::vector<T>& bits, TBitblaster<T>* bb) {
  Trace("bitvector-bb") << "theory::bv::DefaultXorBB bitblasting " << node << "\n";

  Assert(node.getKind() == kind::BITVECTOR_XOR && bits.size() == 0);

  bb->bbTerm(node[0], bits);
  std::vector<T> current;
  for(unsigned j = 1; j < node.getNumChildren(); ++j) {
    bb->bbTerm(node[j], current);
    for (unsigned i = 0; i < utils::getSize(node); ++i) {
      bits[i] = mkXor(bits[i], current[i]);
    }
    current.clear();
  }
  Assert(bits.size() == utils::getSize(node));
}

template <class T>
void DefaultXnorBB (TNode node, std::vector<T>& bits, TBitblaster<T>* bb) {
  Trace("bitvector-bb") << "theory::bv::DefaultXnorBB bitblasting " << node << "\n";

  Assert(node.getNumChildren() == 2 && node.getKind() == kind::BITVECTOR_XNOR
         && bits.size() == 0);
  std::vector<T> lhs, rhs;
  bb->bbTerm(node[0], lhs);
  bb->bbTerm(node[1], rhs);
  Assert(lhs.size() == rhs.size());

  for (unsigned i = 0; i < lhs.size(); ++i) {
    bits.push_back(mkIff(lhs[i], rhs[i])); 
  }
}


template <class T>
void DefaultNandBB (TNode node, std::vector<T>& bits, TBitblaster<T>* bb) {
  Trace("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
template <class T>
void DefaultNorBB (TNode node, std::vector<T>& bits, TBitblaster<T>* bb) {
  Trace("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
template <class T>
void DefaultCompBB (TNode node, std::vector<T>& bits, TBitblaster<T>* bb) {
  Trace("bitvector") << "theory::bv:: DefaultCompBB bitblasting "<< node << "\n";

  Assert(utils::getSize(node) == 1 && bits.size() == 0
         && node.getKind() == kind::BITVECTOR_COMP);
  std::vector<T> a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);

  std::vector<T> bit_eqs;
  for (unsigned i = 0; i < a.size(); ++i) {
    T eq = mkIff(a[i], b[i]);
    bit_eqs.push_back(eq); 
  }
  T a_eq_b = mkAnd(bit_eqs);
  bits.push_back(a_eq_b);   
}

template <class T>
void DefaultMultBB (TNode node, std::vector<T>& res, TBitblaster<T>* bb) {
  Trace("bitvector") << "theory::bv:: DefaultMultBB bitblasting "<< node << "\n";
  Assert(res.size() == 0 && node.getKind() == kind::BITVECTOR_MULT);

  // if (node.getNumChildren() == 2) {
  //   std::vector<T> a;
  //   std::vector<T> b;
  //   bb->bbTerm(node[0], a);
  //   bb->bbTerm(node[1], b);
  //   unsigned bw = utils::getSize(node);
  //   unsigned thresh = bw % 2 ? bw/2 : bw/2 - 1;
  //   bool no_overflow = true; 
  //   for (unsigned i = thresh; i < bw; ++i) {
  //     if (a[i] != mkFalse<T> || b[i] != mkFalse<T> ) {
  //       no_overflow = false; 
  //     }
  //   }
  //   if (no_overflow) {
  //     shiftAddMultiplier(); 
  //     return; 
  //   }
    
  // }
  
  std::vector<T> newres; 
  bb->bbTerm(node[0], res); 
  for(unsigned i = 1; i < node.getNumChildren(); ++i) {
    std::vector<T> current;
    bb->bbTerm(node[i], current);
    newres.clear(); 
    // constructs a simple shift and add multiplier building the result
    // in res
    shiftAddMultiplier(res, current, newres);
    res = newres;
  }
  if(TraceIsOn("bitvector-bb")) {
    Trace("bitvector-bb") << "with bits: " << toString(res)  << "\n";
  }
}

template <class T>
void DefaultAddBB(TNode node, std::vector<T>& res, TBitblaster<T>* bb)
{
  Trace("bitvector-bb") << "theory::bv::DefaultAddBB bitblasting " << node
                        << "\n";
  Assert(node.getKind() == kind::BITVECTOR_ADD && res.size() == 0);

  bb->bbTerm(node[0], res);

  std::vector<T> newres;

  for(unsigned i = 1; i < node.getNumChildren(); ++i) {
    std::vector<T> current;
    bb->bbTerm(node[i], current);
    newres.clear(); 
    rippleCarryAdder(res, current, newres, mkFalse<T>());
    res = newres; 
  }

  Assert(res.size() == utils::getSize(node));
}

template <class T>
void DefaultSubBB (TNode node, std::vector<T>& bits, TBitblaster<T>* bb) {
  Trace("bitvector-bb") << "theory::bv::DefaultSubBB bitblasting " << node << "\n";
  Assert(node.getKind() == kind::BITVECTOR_SUB && node.getNumChildren() == 2
         && bits.size() == 0);

  std::vector<T> a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);
  Assert(a.size() == b.size() && utils::getSize(node) == a.size());

  // bvsub a b = adder(a, ~b, 1)
  std::vector<T> not_b;
  negateBits(b, not_b);
  rippleCarryAdder(a, not_b, bits, mkTrue<T>());
}

template <class T>
void DefaultNegBB (TNode node, std::vector<T>& bits, TBitblaster<T>* bb) {
  Trace("bitvector-bb") << "theory::bv::DefaultNegBB bitblasting " << node << "\n";
  Assert(node.getKind() == kind::BITVECTOR_NEG);

  std::vector<T> a;
  bb->bbTerm(node[0], a);
  Assert(utils::getSize(node) == a.size());

  // -a = add(~a, 0, 1).
  std::vector<T> not_a;
  negateBits(a, not_a);
  std::vector<T> zero;
  makeZero(zero, utils::getSize(node)); 
  
  rippleCarryAdder(not_a, zero, bits, mkTrue<T>()); 
}

template <class T>
void uDivModRec(const std::vector<T>& a, const std::vector<T>& b, std::vector<T>& q, std::vector<T>& r, unsigned rec_width) {
  Assert(q.size() == 0 && r.size() == 0);

  if(rec_width == 0 || isZero(a)) {
    makeZero(q, a.size());
    makeZero(r, a.size());
    return;
  } 
  
  std::vector<T> q1, r1;
  std::vector<T> a1 = a;
  rshift(a1, 1); 

  uDivModRec(a1, b, q1, r1, rec_width - 1);
  // shift the quotient and remainder (i.e. multiply by two) and add 1 to remainder if a is odd
  lshift(q1, 1);
  lshift(r1, 1);

  
  T is_odd = mkIff(a[0], mkTrue<T>());
  T one_if_odd = mkIte(is_odd, mkTrue<T>(), mkFalse<T>()); 

  std::vector<T> zero;
  makeZero(zero, b.size());
  
  std::vector<T> r1_shift_add;
  // account for a being odd
  rippleCarryAdder(r1, zero, r1_shift_add, one_if_odd); 
  // now check if the remainder is greater than b
  std::vector<T> not_b;
  negateBits(b, not_b);
  std::vector<T> r_minus_b;
  T co1;
  // use adder because we need r_minus_b anyway
  co1 = rippleCarryAdder(r1_shift_add, not_b, r_minus_b, mkTrue<T>()); 
  // sign is true if r1 < b
  T sign = mkNot(co1); 
  
  q1[0] = mkIte(sign, q1[0], mkTrue<T>());

  // would be nice to have a high level ITE instead of bitwise
  for(unsigned i = 0; i < a.size(); ++i) {
    r1_shift_add[i] = mkIte(sign, r1_shift_add[i], r_minus_b[i]); 
  }

  // check if a < b

  std::vector<T> a_minus_b;
  T co2 = rippleCarryAdder(a, not_b, a_minus_b, mkTrue<T>());
  // Node a_lt_b = a_minus_b.back();
  T a_lt_b = mkNot(co2); 
  
  for(unsigned i = 0; i < a.size(); ++i) {
    T qval = mkIte(a_lt_b, mkFalse<T>(), q1[i]);
    T rval = mkIte(a_lt_b, a[i], r1_shift_add[i]);
    q.push_back(qval);
    r.push_back(rval); 
  }

}

template <class T>
void UdivUremBB(TNode node,
                std::vector<T>& quot,
                std::vector<T>& rem,
                TBitblaster<T>* bb)
{
  Trace("bitvector-bb") << "theory::bv::DefaultUdivBB bitblasting " << node
                        << "\n";
  Assert(quot.empty());
  Assert(rem.empty());
  Assert(node.getKind() == kind::BITVECTOR_UDIV
         || node.getKind() == kind::BITVECTOR_UREM);

  std::vector<T> a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);

  uDivModRec(a, b, quot, rem, utils::getSize(node));
  // adding a special case for division by 0
  std::vector<T> iszero;
  for (size_t i = 0, size = b.size(); i < size; ++i)
  {
    iszero.push_back(mkIff(b[i], mkFalse<T>()));
  }
  T b_is_0 = mkAnd(iszero);

  for (size_t i = 0, size = quot.size(); i < size; ++i)
  {
    quot[i] = mkIte(b_is_0, mkTrue<T>(), quot[i]);  // a udiv 0 is 11..11
    rem[i] = mkIte(b_is_0, a[i], rem[i]);           // a urem 0 is a
  }
}

template <class T>
void DefaultUdivBB(TNode node, std::vector<T>& quot, TBitblaster<T>* bb)
{
  Trace("bitvector-bb") << "theory::bv::DefaultUdivBB bitblasting " << node
                        << "\n";
  Assert(quot.empty());
  Assert(node.getKind() == kind::BITVECTOR_UDIV);

  std::vector<T> r;
  UdivUremBB(node, quot, r, bb);
}

template <class T>
void DefaultUremBB(TNode node, std::vector<T>& rem, TBitblaster<T>* bb)
{
  Trace("bitvector-bb") << "theory::bv::DefaultUremBB bitblasting " << node
                        << "\n";
  Assert(rem.empty());
  Assert(node.getKind() == kind::BITVECTOR_UREM);

  std::vector<T> q;
  UdivUremBB(node, q, rem, bb);
}

template <class T>
void DefaultSdivBB (TNode node, std::vector<T>& bits, TBitblaster<T>* bb) {
  Trace("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
template <class T>
void DefaultSremBB (TNode node, std::vector<T>& bits, TBitblaster<T>* bb) {
  Trace("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
template <class T>
void DefaultSmodBB (TNode node, std::vector<T>& bits, TBitblaster<T>* bb) {
  Trace("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}

template <class T>
void DefaultShlBB(TNode node, std::vector<T>& res, TBitblaster<T>* bb)
{
  Trace("bitvector-bb") << "theory::bv::DefaultShlBB bitblasting " << node
                        << "\n";
  Assert(node.getKind() == kind::BITVECTOR_SHL && res.size() == 0);
  std::vector<T> a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);

  // check for b < log2(n)
  unsigned size = utils::getSize(node);
  unsigned log2_size = std::ceil(log2((double)size));
  Node a_size = utils::mkConst(size, size);

  std::vector<T> a_size_bits;
  DefaultConstBB(a_size, a_size_bits, bb);
  T b_ult_a_size = uLessThanBB(b, a_size_bits, false);

  std::vector<T> prev_res;
  res = a;
  // we only need to look at the bits bellow log2_a_size
  for (unsigned s = 0; s < log2_size; ++s)
  {
    // barrel shift stage: at each stage you can either shift by 2^s bits
    // or leave the previous stage untouched
    prev_res = res;
    unsigned threshold = pow(2, s);
    for (unsigned i = 0; i < a.size(); ++i)
    {
      if (i < threshold)
      {
        // if b[s] is true then we must have shifted by at least 2^b bits so
        // all bits bellow 2^s will be 0, otherwise just use previous shift
        // value
        res[i] = mkIte(b[s], mkFalse<T>(), prev_res[i]);
      }
      else
      {
        // if b[s]= 0, use previous value, otherwise shift by threshold  bits
        Assert(i >= threshold);
        res[i] = mkIte(b[s], prev_res[i - threshold], prev_res[i]);
      }
    }
  }
  prev_res = res;
  for (unsigned i = 0; i < b.size(); ++i)
  {
    // this is fine  because b_ult_a_size has been bit-blasted
    res[i] = mkIte(b_ult_a_size, prev_res[i], mkFalse<T>());
  }

  if (TraceIsOn("bitvector-bb"))
  {
    Trace("bitvector-bb") << "with bits: " << toString(res) << "\n";
  }
}

template <class T>
void DefaultLshrBB(TNode node, std::vector<T>& res, TBitblaster<T>* bb)
{
  Trace("bitvector-bb") << "theory::bv::DefaultLshrBB bitblasting " << node
                        << "\n";
  Assert(node.getKind() == kind::BITVECTOR_LSHR && res.size() == 0);
  std::vector<T> a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);

  // check for b < log2(n)
  unsigned size = utils::getSize(node);
  unsigned log2_size = std::ceil(log2((double)size));
  Node a_size = utils::mkConst(size, size);

  std::vector<T> a_size_bits;
  DefaultConstBB(a_size, a_size_bits, bb);
  T b_ult_a_size = uLessThanBB(b, a_size_bits, false);

  res = a;
  std::vector<T> prev_res;

  for (unsigned s = 0; s < log2_size; ++s)
  {
    // barrel shift stage: at each stage you can either shift by 2^s bits
    // or leave the previous stage untouched
    prev_res = res;
    int threshold = pow(2, s);
    for (unsigned i = 0; i < a.size(); ++i)
    {
      if (i + threshold >= a.size())
      {
        // if b[s] is true then we must have shifted by at least 2^b bits so
        // all bits above 2^s will be 0, otherwise just use previous shift value
        res[i] = mkIte(b[s], mkFalse<T>(), prev_res[i]);
      }
      else
      {
        // if b[s]= 0, use previous value, otherwise shift by threshold  bits
        Assert(i + threshold < a.size());
        res[i] = mkIte(mkNot(b[s]), prev_res[i], prev_res[i + threshold]);
      }
    }
  }

  prev_res = res;
  for (unsigned i = 0; i < b.size(); ++i)
  {
    // this is fine  because b_ult_a_size has been bit-blasted
    res[i] = mkIte(b_ult_a_size, prev_res[i], mkFalse<T>());
  }

  if (TraceIsOn("bitvector-bb"))
  {
    Trace("bitvector-bb") << "with bits: " << toString(res) << "\n";
  }
}

template <class T>
void DefaultAshrBB(TNode node, std::vector<T>& res, TBitblaster<T>* bb)
{
  Trace("bitvector-bb") << "theory::bv::DefaultAshrBB bitblasting " << node
                        << "\n";
  Assert(node.getKind() == kind::BITVECTOR_ASHR && res.size() == 0);
  std::vector<T> a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);

  //   check for b < n
  unsigned size = utils::getSize(node);
  unsigned log2_size = std::ceil(log2((double)size));
  Node a_size = utils::mkConst(size, size);

  std::vector<T> a_size_bits;
  DefaultConstBB(a_size, a_size_bits, bb);
  T b_ult_a_size = uLessThanBB(b, a_size_bits, false);

  res = a;
  T sign_bit = a.back();
  std::vector<T> prev_res;

  for (unsigned s = 0; s < log2_size; ++s)
  {
    // barrel shift stage: at each stage you can either shift by 2^s bits
    // or leave the previous stage untouched
    prev_res = res;
    int threshold = pow(2, s);
    for (unsigned i = 0; i < a.size(); ++i)
    {
      if (i + threshold >= a.size())
      {
        // if b[s] is true then we must have shifted by at least 2^b bits so
        // all bits above 2^s will be the sign bit, otherwise just use previous
        // shift value
        res[i] = mkIte(b[s], sign_bit, prev_res[i]);
      }
      else
      {
        // if b[s]= 0, use previous value, otherwise shift by threshold  bits
        Assert(i + threshold < a.size());
        res[i] = mkIte(mkNot(b[s]), prev_res[i], prev_res[i + threshold]);
      }
    }
  }

  prev_res = res;
  for (unsigned i = 0; i < b.size(); ++i)
  {
    // this is fine  because b_ult_a_size has been bit-blasted
    res[i] = mkIte(b_ult_a_size, prev_res[i], sign_bit);
  }

  if (TraceIsOn("bitvector-bb"))
  {
    Trace("bitvector-bb") << "with bits: " << toString(res) << "\n";
  }
}

template <class T>
void DefaultUltbvBB (TNode node, std::vector<T>& res, TBitblaster<T>* bb) {
  Trace("bitvector-bb") << "Bitblasting node " << node  << "\n";
  Assert(node.getKind() == kind::BITVECTOR_ULTBV);
  std::vector<T> a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);
  Assert(a.size() == b.size());

  // construct bitwise comparison 
  res.push_back(uLessThanBB(a, b, false));
}

template <class T>
void DefaultSltbvBB (TNode node, std::vector<T>& res, TBitblaster<T>* bb) {
  Trace("bitvector-bb") << "Bitblasting node " << node  << "\n";
  Assert(node.getKind() == kind::BITVECTOR_SLTBV);
  std::vector<T> a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);
  Assert(a.size() == b.size());

  // construct bitwise comparison 
  res.push_back(sLessThanBB(a, b, false));
}

template <class T>
void DefaultIteBB (TNode node, std::vector<T>& res, TBitblaster<T>* bb) {
  Trace("bitvector-bb") << "Bitblasting node " << node  << "\n";
  Assert(node.getKind() == kind::BITVECTOR_ITE);
  std::vector<T> cond, thenpart, elsepart;
  bb->bbTerm(node[0], cond);
  bb->bbTerm(node[1], thenpart);
  bb->bbTerm(node[2], elsepart);

  Assert(cond.size() == 1);
  Assert(thenpart.size() == elsepart.size());

  for (unsigned i = 0; i < thenpart.size(); ++i) {
    // (~cond OR thenpart) AND (cond OR elsepart)
    res.push_back(mkAnd(mkOr(mkNot(cond[0]),thenpart[i]),mkOr(cond[0],elsepart[i])));
  }
}

template <class T>
void DefaultExtractBB (TNode node, std::vector<T>& bits, TBitblaster<T>* bb) {
  Assert(node.getKind() == kind::BITVECTOR_EXTRACT);
  Assert(bits.size() == 0);

  std::vector<T> base_bits;
  bb->bbTerm(node[0], base_bits);
  unsigned high = utils::getExtractHigh(node);
  unsigned low  = utils::getExtractLow(node);

  for (unsigned i = low; i <= high; ++i) {
    bits.push_back(base_bits[i]); 
  }
  Assert(bits.size() == high - low + 1);

  if(TraceIsOn("bitvector-bb")) {
    Trace("bitvector-bb") << "theory::bv::DefaultExtractBB bitblasting " << node << "\n";
    Trace("bitvector-bb") << "                               with bits " << toString(bits); 
  }
}


template <class T>
void DefaultRepeatBB (TNode node, std::vector<T>& bits, TBitblaster<T>* bb) {
  Trace("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  // this should be rewritten 
  Unimplemented(); 
}

template <class T>
void DefaultZeroExtendBB (TNode node, std::vector<T>& res_bits, TBitblaster<T>* bb) {

  Trace("bitvector-bb") << "theory::bv::DefaultZeroExtendBB bitblasting " << node  << "\n";
 
  // this should be rewritten 
  Unimplemented();
  
}

template <class T>
void DefaultSignExtendBB (TNode node, std::vector<T>& res_bits, TBitblaster<T>* bb) {
  Trace("bitvector-bb") << "theory::bv::DefaultSignExtendBB bitblasting " << node  << "\n";

  Assert(node.getKind() == kind::BITVECTOR_SIGN_EXTEND && res_bits.size() == 0);

  std::vector<T> bits;
  bb->bbTerm(node[0], bits);
  
  T sign_bit = bits.back();
  unsigned amount =
      node.getOperator().getConst<BitVectorSignExtend>().d_signExtendAmount;

  for (unsigned i = 0; i < bits.size(); ++i ) {
    res_bits.push_back(bits[i]); 
  }
         
  for (unsigned i = 0 ; i < amount ; ++i ) {
    res_bits.push_back(sign_bit); 
  }

  Assert(res_bits.size() == amount + bits.size());
}

template <class T>
void DefaultRotateRightBB (TNode node, std::vector<T>& res, TBitblaster<T>* bb) {
  Trace("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";

  Unimplemented(); 
}

template <class T>
void DefaultRotateLeftBB (TNode node, std::vector<T>& bits, TBitblaster<T>* bb) {
  Trace("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}


}
}
}  // namespace cvc5::internal

#endif
