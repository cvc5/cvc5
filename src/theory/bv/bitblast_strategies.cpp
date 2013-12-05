/*********************                                                        */
/*! \file bitblast_strategies.cpp
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): Clark Barrett, Dejan Jovanovic, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of bitblasting functions for various operators. 
 **
 ** Implementation of bitblasting functions for various operators. 
 **/

#include "bitblast_strategies.h"
#include "bitblaster.h"
#include "prop/sat_solver.h"
#include "theory/booleans/theory_bool_rewriter.h"
#include <cmath>

using namespace CVC4::prop; 
using namespace CVC4::theory::bv::utils;
namespace CVC4 {
namespace theory {
namespace bv {

/*
  Purely debugging
 */

Bits* rewriteBits(const Bits& bits) {
  Bits* newbits = new Bits(); 
  for (unsigned i = 0; i < bits.size(); ++i) {
    newbits->push_back(Rewriter::rewrite(bits[i])); 
  }
  return newbits;
}

Node rewrite(TNode node) {
  return Rewriter::rewrite(node); 
}

/*
 Various helper functions that get called by the bitblasting procedures
 */

void inline extractBits(const Bits& b, Bits& dest, unsigned lo, unsigned hi) {
  Assert ( lo < b.size() && hi < b.size() && lo <= hi);
  for (unsigned i = lo; i <= hi; ++i) {
    dest.push_back(b[i]); 
  }
}

void inline negateBits(const Bits& bits, Bits& negated_bits) {
  for(unsigned i = 0; i < bits.size(); ++i) {
    negated_bits.push_back(utils::mkNot(bits[i])); 
  }
}

bool inline isZero(const Bits& bits) {
  for(unsigned i = 0; i < bits.size(); ++i) {
    if(bits[i] != mkFalse()) {
      return false; 
    }
  }
  return true; 
}

void inline rshift(Bits& bits, unsigned amount) {
  for (unsigned i = 0; i < bits.size() - amount; ++i) {
    bits[i] = bits[i+amount]; 
  }
  for(unsigned i = bits.size() - amount; i < bits.size(); ++i) {
    bits[i] = mkFalse(); 
  }
}

void inline lshift(Bits& bits, unsigned amount) {
  for (int i = (int)bits.size() - 1; i >= (int)amount ; --i) {
    bits[i] = bits[i-amount]; 
  }
  for(unsigned i = 0; i < amount; ++i) {
    bits[i] = mkFalse(); 
  }
}

void inline makeZero(Bits& bits, unsigned width) {
  Assert(bits.size() == 0); 
  for(unsigned i = 0; i < width; ++i) {
    bits.push_back(mkFalse()); 
  }
}


/** 
 * Constructs a simple ripple carry adder
 * 
 * @param a first term to be added
 * @param b second term to be added
 * @param res the result
 * @param carry the carry-in bit 
 * 
 * @return the carry-out
 */
Node inline rippleCarryAdder(const Bits&a, const Bits& b, Bits& res, Node carry) {
  Assert(a.size() == b.size() && res.size() == 0);
  
  for (unsigned i = 0 ; i < a.size(); ++i) {
    Node sum = mkXor(mkXor(a[i], b[i]), carry);
    carry = mkOr( mkAnd(a[i], b[i]),
                  mkAnd( mkXor(a[i], b[i]),
                         carry));
    res.push_back(sum); 
  }

  return carry;
}

inline void shiftAddMultiplier(const Bits&a, const Bits&b, Bits& res) {
  
  for (unsigned i = 0; i < a.size(); ++i) {
    res.push_back(mkNode(kind::AND, b[0], a[i])); 
  }
  
  for(unsigned k = 1; k < res.size(); ++k) {
  Node carry_in = mkFalse();
  Node carry_out;
    for(unsigned j = 0; j < res.size() -k; ++j) {
      Node aj = mkAnd(a[j], b[k]);
      carry_out = mkOr(mkAnd(res[j+k], aj),
                       mkAnd( mkXor(res[j+k], aj), carry_in));
      res[j+k] = mkXor(mkXor(res[j+k], aj), carry_in);
      carry_in = carry_out; 
    }
  }
}

Node inline uLessThanBB(const Bits&a, const Bits& b, bool orEqual) {
  Assert (a.size() && b.size());
  
  Node res = mkNode(kind::AND, mkNode(kind::NOT, a[0]), b[0]);
  
  if(orEqual) {
    res = mkNode(kind::OR, res, mkNode(kind::IFF, a[0], b[0])); 
  }
  
  for (unsigned i = 1; i < a.size(); ++i) {
    // a < b iff ( a[i] <-> b[i] AND a[i-1:0] < b[i-1:0]) OR (~a[i] AND b[i]) 
    res = mkNode(kind::OR,
                 mkNode(kind::AND, mkNode(kind::IFF, a[i], b[i]), res),
                 mkNode(kind::AND, mkNode(kind::NOT, a[i]), b[i])); 
  }
  return res;
}

Node inline sLessThanBB(const Bits&a, const Bits& b, bool orEqual) {
  Assert (a.size() && b.size());
  if (a.size() == 1) {
    if(orEqual) {
      return  mkNode(kind::OR,
                     mkNode(kind::IFF, a[0], b[0]),
                     mkNode(kind::AND, a[0], mkNode(kind::NOT, b[0]))); 
    }

    return mkNode(kind::AND, a[0], mkNode(kind::NOT, b[0]));
  }
  unsigned n = a.size() - 1; 
  Bits a1, b1;
  extractBits(a, a1, 0, n-1);
  extractBits(b, b1, 0, n-1);
  
  // unsigned comparison of the first n-1 bits
  Node ures = uLessThanBB(a1, b1, orEqual);
  Node res = mkNode(kind::OR,
                    // a b have the same sign
                    mkNode(kind::AND,
                           mkNode(kind::IFF, a[n], b[n]),
                           ures),
                    // a is negative and b positive
                    mkNode(kind::AND,
                           a[n],
                           mkNode(kind::NOT, b[n])));
  return res;
}


/*
  Atom bitblasting strategies 
 */


Node UndefinedAtomBBStrategy(TNode node, Bitblaster* bb) {
  Debug("bitvector") << "TheoryBV::Bitblaster Undefined bitblasting strategy for kind: "
                     << node.getKind() << "\n";
  Unreachable(); 
}

Node DefaultEqBB(TNode node, Bitblaster* bb) {
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";
  
  Assert(node.getKind() == kind::EQUAL);
  Bits lhs, rhs; 
  bb->bbTerm(node[0], lhs);
  bb->bbTerm(node[1], rhs);

  Assert(lhs.size() == rhs.size());

  NodeManager* nm = NodeManager::currentNM();

  std::vector<Node> bits_eq;
  for (unsigned i = 0; i < lhs.size(); i++) {
    Node bit_eq = nm->mkNode(kind::IFF, lhs[i], rhs[i]);
    bits_eq.push_back(bit_eq); 
  }
  Node bv_eq = utils::mkAnd(bits_eq);
  return bv_eq; 
}


Node AdderUltBB(TNode node, Bitblaster* bb) {
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";
  Assert(node.getKind() == kind::BITVECTOR_ULT);
  Bits a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);
  Assert(a.size() == b.size());
  
  // a < b <=> ~ (add(a, ~b, 1).carry_out)
  Bits not_b;
  negateBits(b, not_b);
  Node carry = mkTrue();
  
  for (unsigned i = 0 ; i < a.size(); ++i) {
    carry = mkOr( mkAnd(a[i], not_b[i]),
                  mkAnd( mkXor(a[i], not_b[i]),
                         carry));
  }
  return mkNot(carry); 
}


Node DefaultUltBB(TNode node, Bitblaster* bb) {
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";
  Assert(node.getKind() == kind::BITVECTOR_ULT);
  Bits a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);
  Assert(a.size() == b.size());
  
  // construct bitwise comparison 
  Node res = uLessThanBB(a, b, false);
  return res; 
}

Node DefaultUleBB(TNode node, Bitblaster* bb){
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";
  Assert(node.getKind() == kind::BITVECTOR_ULE);
  Bits a, b;
  
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);
  Assert(a.size() == b.size());
  // construct bitwise comparison 
  Node res = uLessThanBB(a, b, true);
  return res; 
}

Node DefaultUgtBB(TNode node, Bitblaster* bb){
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";
  // should be rewritten 
  Unimplemented(); 
}
Node DefaultUgeBB(TNode node, Bitblaster* bb){
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";
  // should be rewritten 
  Unimplemented(); 
}

// Node DefaultSltBB(TNode node, Bitblaster* bb){
//   Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";
//   // shoudl be rewritten in terms of ult
//   Unimplemented(); 
// }

// Node DefaultSleBB(TNode node, Bitblaster* bb){
//   Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";
//   // shoudl be rewritten in terms of ule
//   Unimplemented(); 
// }


Node DefaultSltBB(TNode node, Bitblaster* bb){
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";

  Bits a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);
  Assert(a.size() == b.size());
  
  Node res = sLessThanBB(a, b, false); 
  return res;
}

Node DefaultSleBB(TNode node, Bitblaster* bb){
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";

  Bits a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);
  Assert(a.size() == b.size());
  
  Node res = sLessThanBB(a, b, true); 
  return res;
}
 
Node DefaultSgtBB(TNode node, Bitblaster* bb){
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";
  // should be rewritten 
  Unimplemented(); 
}

Node DefaultSgeBB(TNode node, Bitblaster* bb){
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";
  // should be rewritten 
  Unimplemented(); 
}


/// Term bitblasting strategies 

void UndefinedTermBBStrategy(TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Undefined bitblasting strategy for kind: "
                     << node.getKind() << "\n";
  Unreachable(); 
}

void DefaultVarBB (TNode node, Bits& bits, Bitblaster* bb) {
  Assert(bits.size() == 0);
  for (unsigned i = 0; i < utils::getSize(node); ++i) {
    bits.push_back(utils::mkBitOf(node, i));
  }

  if(Debug.isOn("bitvector-bb")) {
    Debug("bitvector-bb") << "theory::bv::DefaultVarBB bitblasting  " << node << "\n";
    Debug("bitvector-bb") << "                           with bits  " << toString(bits); 
  }

   bb->storeVariable(node);
}

void DefaultConstBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultConstBB bitblasting " << node << "\n";
  Assert(node.getKind() == kind::CONST_BITVECTOR);
  Assert(bits.size() == 0);
  
  for (unsigned i = 0; i < utils::getSize(node); ++i) {
    Integer bit = node.getConst<BitVector>().extract(i, i).getValue();
    if(bit == Integer(0)){
      bits.push_back(utils::mkFalse());
    } else {
      Assert (bit == Integer(1));
      bits.push_back(utils::mkTrue()); 
    }
  }
  if(Debug.isOn("bitvector-bb")) {
    Debug("bitvector-bb") << "with  bits: " << toString(bits) << "\n"; 
  }
}


void DefaultNotBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultNotBB bitblasting " << node << "\n";
  Assert(node.getKind() == kind::BITVECTOR_NOT);
  Assert(bits.size() == 0);
  Bits bv; 
  bb->bbTerm(node[0], bv);
  negateBits(bv, bits);
}

void DefaultConcatBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultConcatBB bitblasting " << node << "\n";
  Assert(bits.size() == 0);
  
  Assert (node.getKind() == kind::BITVECTOR_CONCAT);
  for (int i = node.getNumChildren() -1 ; i >= 0; --i ) {
    TNode current = node[i];
    Bits current_bits; 
    bb->bbTerm(current, current_bits);

    for(unsigned j = 0; j < utils::getSize(current); ++j) {
      bits.push_back(current_bits[j]);
    }
  }
  Assert (bits.size() == utils::getSize(node)); 
  if(Debug.isOn("bitvector-bb")) {
    Debug("bitvector-bb") << "with  bits: " << toString(bits) << "\n"; 
  }
}

void DefaultAndBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultAndBB bitblasting " << node << "\n";
  
  Assert(node.getKind() == kind::BITVECTOR_AND &&
         bits.size() == 0);
  
  for(unsigned j = 0; j < utils::getSize(node); ++j) {
    NodeBuilder<> andBuilder(kind::AND);
    for (unsigned i = 0; i < node.getNumChildren(); ++i) {
      Bits current;
      bb->bbTerm(node[i], current);
      andBuilder << current[j];
      Assert(utils::getSize(node) == current.size());
    }
    bits.push_back(andBuilder); 
  }
}

void DefaultOrBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultOrBB bitblasting " << node << "\n";

  Assert(node.getKind() == kind::BITVECTOR_OR &&
         bits.size() == 0);
  
  for(unsigned j = 0; j < utils::getSize(node); ++j) {
    NodeBuilder<> orBuilder(kind::OR);
    for (unsigned i = 0; i < node.getNumChildren(); ++i) {
      Bits current;
      bb->bbTerm(node[i], current);
      orBuilder << current[j];
      Assert(utils::getSize(node) == current.size());
    }
    bits.push_back(orBuilder); 
  }
}

void DefaultXorBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultXorBB bitblasting " << node << "\n";

  Assert(node.getKind() == kind::BITVECTOR_XOR &&
         bits.size() == 0);
  
  for(unsigned j = 0; j < utils::getSize(node); ++j) {
    Bits first;
    bb->bbTerm(node[0], first); 
    Node bitj = first[j];
    
    for (unsigned i = 1; i < node.getNumChildren(); ++i) {
      Bits current;
      bb->bbTerm(node[i], current);
      bitj = utils::mkNode(kind::XOR, bitj, current[j]);
      Assert(utils::getSize(node) == current.size());
    }
    bits.push_back(bitj); 
  }
}

void DefaultXnorBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultXnorBB bitblasting " << node << "\n";

  Assert(node.getNumChildren() == 2 &&
         node.getKind() == kind::BITVECTOR_XNOR &&
         bits.size() == 0);
  Bits lhs, rhs;
  bb->bbTerm(node[0], lhs);
  bb->bbTerm(node[1], rhs);
  Assert(lhs.size() == rhs.size()); 
  
  for (unsigned i = 0; i < lhs.size(); ++i) {
    bits.push_back(utils::mkNode(kind::IFF, lhs[i], rhs[i])); 
  }
}


void DefaultNandBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
void DefaultNorBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
void DefaultCompBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: DefaultCompBB bitblasting "<< node << "\n";

  Assert(getSize(node) == 1 && bits.size() == 0 && node.getKind() == kind::BITVECTOR_COMP);
  Bits a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);

  std::vector<Node> bit_eqs;
  NodeManager* nm = NodeManager::currentNM(); 
  for (unsigned i = 0; i < a.size(); ++i) {
    Node eq = nm->mkNode(kind::IFF, a[i], b[i]);
    bit_eqs.push_back(eq); 
  }
  Node a_eq_b = mkAnd(bit_eqs);
  bits.push_back(a_eq_b);   
}

void DefaultMultBB (TNode node, Bits& res, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: DefaultMultBB bitblasting "<< node << "\n";
  Assert(res.size() == 0 &&
         node.getKind() == kind::BITVECTOR_MULT);

  Bits newres; 
  bb->bbTerm(node[0], res); 
  for(unsigned i = 1; i < node.getNumChildren(); ++i) {
    Bits current;
    bb->bbTerm(node[i], current);
    newres.clear(); 
    // constructs a simple shift and add multiplier building the result
    // in res
    shiftAddMultiplier(res, current, newres);
    res = newres;
  }
  if(Debug.isOn("bitvector-bb")) {
    Debug("bitvector-bb") << "with bits: " << toString(res)  << "\n";
  }
}

void DefaultPlusBB (TNode node, Bits& res, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultPlusBB bitblasting " << node << "\n";
  Assert(node.getKind() == kind::BITVECTOR_PLUS &&
         res.size() == 0);

  bb->bbTerm(node[0], res);

  Bits newres;

  for(unsigned i = 1; i < node.getNumChildren(); ++i) {
    Bits current;
    bb->bbTerm(node[i], current);
    newres.clear(); 
    rippleCarryAdder(res, current, newres, utils::mkFalse());
    res = newres; 
  }
  
  Assert(res.size() == utils::getSize(node));
}


void DefaultSubBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultSubBB bitblasting " << node << "\n";
  Assert(node.getKind() == kind::BITVECTOR_SUB &&
         node.getNumChildren() == 2 &&
         bits.size() == 0);
    
  Bits a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b); 
  Assert(a.size() == b.size() && utils::getSize(node) == a.size());

  // bvsub a b = adder(a, ~b, 1)
  Bits not_b;
  negateBits(b, not_b);
  Node carry = utils::mkTrue();
  rippleCarryAdder(a, not_b, bits, mkTrue());
}

void DefaultNegBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultNegBB bitblasting " << node << "\n";
  Assert(node.getKind() == kind::BITVECTOR_NEG);
  
  Bits a;
  bb->bbTerm(node[0], a);
  Assert(utils::getSize(node) == a.size());

  // -a = add(~a, 0, 1).
  Bits not_a;
  negateBits(a, not_a);
  Bits zero;
  makeZero(zero, getSize(node)); 
  
  rippleCarryAdder(not_a, zero, bits, mkTrue()); 
}

void uDivModRec(const Bits& a, const Bits& b, Bits& q, Bits& r, unsigned rec_width) {
  Assert( q.size() == 0 && r.size() == 0);

  if(rec_width == 0 || isZero(a)) {
    makeZero(q, a.size());
    makeZero(r, a.size());
    return;
  } 
  
  Bits q1, r1;
  Bits a1 = a;
  rshift(a1, 1); 

  uDivModRec(a1, b, q1, r1, rec_width - 1);
  // shift the quotient and remainder (i.e. multiply by two) and add 1 to remainder if a is odd
  lshift(q1, 1);
  lshift(r1, 1);

  
  Node is_odd = mkNode(kind::IFF, a[0], mkTrue());
  Node one_if_odd = mkNode(kind::ITE, is_odd, mkTrue(), mkFalse()); 

  Bits zero;
  makeZero(zero, b.size());
  
  Bits r1_shift_add;
  // account for a being odd
  rippleCarryAdder(r1, zero, r1_shift_add, one_if_odd); 
  // now check if the remainder is greater than b
  Bits not_b;
  negateBits(b, not_b);
  Bits r_minus_b;
  Node co1;
  // use adder because we need r_minus_b anyway
  co1 = rippleCarryAdder(r1_shift_add, not_b, r_minus_b, mkTrue()); 
  // sign is true if r1 < b
  Node sign = mkNode(kind::NOT, co1); 
  
  q1[0] = mkNode(kind::ITE, sign, q1[0], mkTrue());

  // would be nice to have a high level ITE instead of bitwise
  for(unsigned i = 0; i < a.size(); ++i) {
    r1_shift_add[i] = mkNode(kind::ITE, sign, r1_shift_add[i], r_minus_b[i]); 
  }

  // check if a < b

  Bits a_minus_b;
  Node co2 = rippleCarryAdder(a, not_b, a_minus_b, mkTrue());
  // Node a_lt_b = a_minus_b.back();
  Node a_lt_b = mkNode(kind::NOT, co2); 
  
  for(unsigned i = 0; i < a.size(); ++i) {
    Node qval = mkNode(kind::ITE, a_lt_b, mkFalse(), q1[i]);
    Node rval = mkNode(kind::ITE, a_lt_b, a[i], r1_shift_add[i]);
    q.push_back(qval);
    r.push_back(rval); 
  }

}

void DefaultUdivBB (TNode node, Bits& q, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultUdivBB bitblasting " << node << "\n";
  Assert(node.getKind() == kind::BITVECTOR_UDIV_TOTAL &&  q.size() == 0);

  Bits a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);

  Bits r;
  uDivModRec(a, b, q, r, getSize(node)); 
  // adding a special case for division by 0
  std::vector<Node> iszero; 
  for (unsigned i = 0; i < b.size(); ++i) {
    iszero.push_back(utils::mkNode(kind::IFF, b[i], utils::mkFalse())); 
  }
  Node b_is_0 = utils::mkAnd(iszero); 
  
  for (unsigned i = 0; i < q.size(); ++i) {
    q[i] = utils::mkNode(kind::ITE, b_is_0, utils::mkFalse(), q[i]);
    r[i] = utils::mkNode(kind::ITE, b_is_0, utils::mkFalse(), r[i]);
  }

  // cache the remainder in case we need it later
  Node remainder = mkNode(kind::BITVECTOR_UREM_TOTAL, node[0], node[1]);
  bb->cacheTermDef(remainder, r);
}

void DefaultUremBB (TNode node, Bits& rem, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultUremBB bitblasting " << node << "\n";
  Assert(node.getKind() == kind::BITVECTOR_UREM_TOTAL &&  rem.size() == 0);

  Bits a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);

  Bits q;
  uDivModRec(a, b, q, rem, getSize(node)); 
  // adding a special case for division by 0
  std::vector<Node> iszero; 
  for (unsigned i = 0; i < b.size(); ++i) {
    iszero.push_back(utils::mkNode(kind::IFF, b[i], utils::mkFalse())); 
  }
  Node b_is_0 = utils::mkAnd(iszero); 
  
  for (unsigned i = 0; i < q.size(); ++i) {
    q[i] = utils::mkNode(kind::ITE, b_is_0, utils::mkFalse(), q[i]);
    rem[i] = utils::mkNode(kind::ITE, b_is_0, utils::mkFalse(), rem[i]);
  }

  // cache the quotient in case we need it later
  Node quotient = mkNode(kind::BITVECTOR_UDIV_TOTAL, node[0], node[1]);
  bb->cacheTermDef(quotient, q);
}


void DefaultSdivBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
void DefaultSremBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
void DefaultSmodBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}

void DefaultShlBB (TNode node, Bits& res, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultShlBB bitblasting " << node  << "\n";
  Assert (node.getKind() == kind::BITVECTOR_SHL &&
          res.size() == 0);
  Bits a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);

  // check for b < log2(n)
  unsigned size = utils::getSize(node);
  unsigned log2_size = std::ceil(log2((double)size));
  Node a_size = utils::mkConst(BitVector(size, size)); 
  Node b_ult_a_size = utils::mkNode(kind::BITVECTOR_ULT, node[1], a_size);
  // ensure that the inequality is bit-blasted
  bb->bbAtom(b_ult_a_size); 
  
  Bits prev_res;
  res = a; 
  // we only need to look at the bits bellow log2_a_size
  for(unsigned s = 0; s < log2_size; ++s) {
    // barrel shift stage: at each stage you can either shift by 2^s bits
    // or leave the previous stage untouched
    prev_res = res; 
    unsigned threshold = pow(2, s); 
    for(unsigned i = 0; i < a.size(); ++i) {
      if (i < threshold) {
        // if b[s] is true then we must have shifted by at least 2^b bits so
        // all bits bellow 2^s will be 0, otherwise just use previous shift value
        res[i] = mkNode(kind::ITE, b[s], mkFalse(), prev_res[i]);
      } else {
        // if b[s]= 0, use previous value, otherwise shift by threshold  bits
        Assert(i >= threshold); 
        res[i] = mkNode(kind::ITE, b[s], prev_res[i-threshold], prev_res[i]); 
      }
    }
  }
  prev_res = res;
  for (unsigned i = 0; i < b.size(); ++i) {
    // this is fine  because b_ult_a_size has been bit-blasted
    res[i] = utils::mkNode(kind::ITE, b_ult_a_size, prev_res[i], utils::mkFalse()); 
  }
  
  if(Debug.isOn("bitvector-bb")) {
    Debug("bitvector-bb") << "with bits: " << toString(res)  << "\n";
  }
}

void DefaultLshrBB (TNode node, Bits& res, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultLshrBB bitblasting " << node  << "\n";
  Assert (node.getKind() == kind::BITVECTOR_LSHR &&
          res.size() == 0);
  Bits a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);

  // check for b < log2(n)
  unsigned size = utils::getSize(node);
  unsigned log2_size = std::ceil(log2((double)size));
  Node a_size = utils::mkConst(BitVector(size, size)); 
  Node b_ult_a_size = utils::mkNode(kind::BITVECTOR_ULT, node[1], a_size);
  // ensure that the inequality is bit-blasted
  bb->bbAtom(b_ult_a_size); 
  
  res = a;
  Bits prev_res;
  
  for(unsigned s = 0; s < log2_size; ++s) {
    // barrel shift stage: at each stage you can either shift by 2^s bits
    // or leave the previous stage untouched
    prev_res = res; 
    int threshold = pow(2, s); 
    for(unsigned i = 0; i < a.size(); ++i) {
      if (i + threshold >= a.size()) {
        // if b[s] is true then we must have shifted by at least 2^b bits so
        // all bits above 2^s will be 0, otherwise just use previous shift value
        res[i] = mkNode(kind::ITE, b[s], mkFalse(), prev_res[i]);
      } else {
        // if b[s]= 0, use previous value, otherwise shift by threshold  bits
        Assert (i+ threshold < a.size()); 
        res[i] = mkNode(kind::ITE, mkNot(b[s]), prev_res[i], prev_res[i+threshold]);
      }
    }
  }
  
  prev_res = res;
  for (unsigned i = 0; i < b.size(); ++i) {
    // this is fine  because b_ult_a_size has been bit-blasted
    res[i] = utils::mkNode(kind::ITE, b_ult_a_size, prev_res[i], utils::mkFalse()); 
  }

  if(Debug.isOn("bitvector-bb")) {
    Debug("bitvector-bb") << "with bits: " << toString(res)  << "\n";
  }
}

void DefaultAshrBB (TNode node, Bits& res, Bitblaster* bb) {

  Debug("bitvector-bb") << "theory::bv::DefaultAshrBB bitblasting " << node  << "\n";
  Assert (node.getKind() == kind::BITVECTOR_ASHR &&
          res.size() == 0);
  Bits a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);

  //   check for b < n
  unsigned size = utils::getSize(node);
  unsigned log2_size = std::ceil(log2((double)size));
  Node a_size = utils::mkConst(BitVector(size, size)); 
  Node b_ult_a_size = utils::mkNode(kind::BITVECTOR_ULT, node[1], a_size);
  // ensure that the inequality is bit-blasted
  bb->bbAtom(b_ult_a_size); 
  
  res = a;
  TNode sign_bit = a.back();
  Bits prev_res;

  for(unsigned s = 0; s < log2_size; ++s) {
    // barrel shift stage: at each stage you can either shift by 2^s bits
    // or leave the previous stage untouched
    prev_res = res; 
    int threshold = pow(2, s); 
    for(unsigned i = 0; i < a.size(); ++i) {
      if (i + threshold >= a.size()) {
        // if b[s] is true then we must have shifted by at least 2^b bits so
        // all bits above 2^s will be the sign bit, otherwise just use previous shift value
        res[i] = mkNode(kind::ITE, b[s], sign_bit, prev_res[i]);
      } else {
        // if b[s]= 0, use previous value, otherwise shift by threshold  bits
        Assert (i+ threshold < a.size()); 
        res[i] = mkNode(kind::ITE, mkNot(b[s]), prev_res[i], prev_res[i+threshold]);
      }
    }
  }

  prev_res = res;
  for (unsigned i = 0; i < b.size(); ++i) {
    // this is fine  because b_ult_a_size has been bit-blasted
    res[i] = utils::mkNode(kind::ITE, b_ult_a_size, prev_res[i], sign_bit); 
  }

  if(Debug.isOn("bitvector-bb")) {
    Debug("bitvector-bb") << "with bits: " << toString(res)  << "\n";
  }
}

void DefaultExtractBB (TNode node, Bits& bits, Bitblaster* bb) {
  Assert (node.getKind() == kind::BITVECTOR_EXTRACT);
  Assert(bits.size() == 0);
  
  Bits base_bits;
  bb->bbTerm(node[0], base_bits);
  unsigned high = utils::getExtractHigh(node);
  unsigned low  = utils::getExtractLow(node);

  for (unsigned i = low; i <= high; ++i) {
    bits.push_back(base_bits[i]); 
  }
  Assert (bits.size() == high - low + 1);   

  if(Debug.isOn("bitvector-bb")) {
    Debug("bitvector-bb") << "theory::bv::DefaultExtractBB bitblasting " << node << "\n";
    Debug("bitvector-bb") << "                               with bits " << toString(bits); 
  }
}


void DefaultRepeatBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  // this should be rewritten 
  Unimplemented(); 
}

void DefaultZeroExtendBB (TNode node, Bits& res_bits, Bitblaster* bb) {

  Debug("bitvector-bb") << "theory::bv::DefaultZeroExtendBB bitblasting " << node  << "\n";
 
  // this should be rewritten 
  Unimplemented();
  
}

void DefaultSignExtendBB (TNode node, Bits& res_bits, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultSignExtendBB bitblasting " << node  << "\n";

  Assert (node.getKind() == kind::BITVECTOR_SIGN_EXTEND &&
          res_bits.size() == 0);

  Bits bits;
  bb->bbTerm(node[0], bits);
  
  TNode sign_bit = bits.back(); 
  unsigned amount = node.getOperator().getConst<BitVectorSignExtend>().signExtendAmount; 

  for (unsigned i = 0; i < bits.size(); ++i ) {
    res_bits.push_back(bits[i]); 
  }
         
  for (unsigned i = 0 ; i < amount ; ++i ) {
    res_bits.push_back(sign_bit); 
  }
         
  Assert (res_bits.size() == amount + bits.size()); 
}

void DefaultRotateRightBB (TNode node, Bits& res, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";

  Unimplemented(); 
}

void DefaultRotateLeftBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}


}
}
}


