/*********************                                                        */
/*! \file bitblast_utils.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Various utility functions for bit-blasting.
 **
 ** Various utility functions for bit-blasting.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__BITBLAST__UTILS_H
#define __CVC4__BITBLAST__UTILS_H


#include <ostream>
#include "expr/node.h"

#ifdef CVC4_USE_ABC
#include "base/main/main.h"
#include "base/abc/abc.h"

extern "C" {
#include "sat/cnf/cnf.h"
}
#endif

namespace CVC4 {

namespace theory {
namespace bv {

template <class T> class TBitblaster;

template <class T> 
std::string toString (const std::vector<T>& bits);

template <> inline
std::string toString<Node> (const std::vector<Node>& bits) {
  std::ostringstream os;
  for (int i = bits.size() - 1; i >= 0; --i) {
    TNode bit = bits[i];
    if (bit.getKind() == kind::CONST_BOOLEAN) {
      os << (bit.getConst<bool>() ? "1" : "0");
    } else {
      os << bit<< " ";
    }
  }
  os <<"\n";
  return os.str();
} 

template <class T> T mkTrue(); 
template <class T> T mkFalse(); 
template <class T> T mkNot(T a);
template <class T> T mkOr(T a, T b);
template <class T> T mkOr(const std::vector<T>& a);
template <class T> T mkAnd(T a, T b);
template <class T> T mkAnd(const std::vector<T>& a);
template <class T> T mkXor(T a, T b);
template <class T> T mkIff(T a, T b);
template <class T> T mkIte(T cond, T a, T b);


template <> inline
Node mkTrue<Node>() {
  return NodeManager::currentNM()->mkConst<bool>(true);
}

template <> inline
Node mkFalse<Node>() {
  return NodeManager::currentNM()->mkConst<bool>(false);
}

template <> inline
Node mkNot<Node>(Node a) {
  return NodeManager::currentNM()->mkNode(kind::NOT, a);
}

template <> inline
Node mkOr<Node>(Node a, Node b) {
  return NodeManager::currentNM()->mkNode(kind::OR, a, b);
}

template <> inline
Node mkOr<Node>(const std::vector<Node>& children) {
  Assert (children.size());
  if (children.size() == 1)
    return children[0]; 
  return NodeManager::currentNM()->mkNode(kind::OR, children); 
}


template <> inline
Node mkAnd<Node>(Node a, Node b) {
  return NodeManager::currentNM()->mkNode(kind::AND, a, b);
}

template <> inline
Node mkAnd<Node>(const std::vector<Node>& children) {
  Assert (children.size());
  if (children.size() == 1)
    return children[0]; 
  return NodeManager::currentNM()->mkNode(kind::AND, children); 
}


template <> inline
Node mkXor<Node>(Node a, Node b) {
  return NodeManager::currentNM()->mkNode(kind::XOR, a, b);
}

template <> inline
Node mkIff<Node>(Node a, Node b) {
  return NodeManager::currentNM()->mkNode(kind::EQUAL, a, b);
}

template <> inline
Node mkIte<Node>(Node cond, Node a, Node b) {
  return NodeManager::currentNM()->mkNode(kind::ITE, cond, a, b);
}

/*
 Various helper functions that get called by the bitblasting procedures
 */

template <class T>
void inline extractBits(const std::vector<T>& b, std::vector<T>& dest, unsigned lo, unsigned hi) {
  Assert ( lo < b.size() && hi < b.size() && lo <= hi);
  for (unsigned i = lo; i <= hi; ++i) {
    dest.push_back(b[i]); 
  }
}

template <class T>
void inline negateBits(const std::vector<T>& bits, std::vector<T>& negated_bits) {
  for(unsigned i = 0; i < bits.size(); ++i) {
    negated_bits.push_back(mkNot(bits[i])); 
  }
}

template <class T>
bool inline isZero(const std::vector<T>& bits) {
  for(unsigned i = 0; i < bits.size(); ++i) {
    if(bits[i] != mkFalse<T>()) {
      return false; 
    }
  }
  return true; 
}

template <class T>
void inline rshift(std::vector<T>& bits, unsigned amount) {
  for (unsigned i = 0; i < bits.size() - amount; ++i) {
    bits[i] = bits[i+amount]; 
  }
  for(unsigned i = bits.size() - amount; i < bits.size(); ++i) {
    bits[i] = mkFalse<T>(); 
  }
}

template <class T>
void inline lshift(std::vector<T>& bits, unsigned amount) {
  for (int i = (int)bits.size() - 1; i >= (int)amount ; --i) {
    bits[i] = bits[i-amount]; 
  }
  for(unsigned i = 0; i < amount; ++i) {
    bits[i] = mkFalse<T>(); 
  }
}

template <class T>
void inline makeZero(std::vector<T>& bits, unsigned width) {
  Assert(bits.size() == 0); 
  for(unsigned i = 0; i < width; ++i) {
    bits.push_back(mkFalse<T>()); 
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
template <class T>
T inline rippleCarryAdder(const std::vector<T>&a, const std::vector<T>& b, std::vector<T>& res, T carry) {
  Assert(a.size() == b.size() && res.size() == 0);
  
  for (unsigned i = 0 ; i < a.size(); ++i) {
    T sum = mkXor(mkXor(a[i], b[i]), carry);
    carry = mkOr( mkAnd(a[i], b[i]),
                  mkAnd( mkXor(a[i], b[i]),
                         carry));
    res.push_back(sum); 
  }

  return carry;
}

template <class T>
inline void shiftAddMultiplier(const std::vector<T>&a, const std::vector<T>&b, std::vector<T>& res) {
  
  for (unsigned i = 0; i < a.size(); ++i) {
    res.push_back(mkAnd(b[0], a[i])); 
  }
  
  for(unsigned k = 1; k < res.size(); ++k) {
  T carry_in = mkFalse<T>();
  T carry_out;
    for(unsigned j = 0; j < res.size() -k; ++j) {
      T aj = mkAnd(b[k], a[j]);
      carry_out = mkOr(mkAnd(res[j+k], aj),
                       mkAnd( mkXor(res[j+k], aj), carry_in));
      res[j+k] = mkXor(mkXor(res[j+k], aj), carry_in);
      carry_in = carry_out; 
    }
  }
}

template <class T>
T inline uLessThanBB(const std::vector<T>&a, const std::vector<T>& b, bool orEqual) {
  Assert (a.size() && b.size());
  
  T res = mkAnd(mkNot(a[0]), b[0]);
  
  if(orEqual) {
    res = mkOr(res, mkIff(a[0], b[0])); 
  }
  
  for (unsigned i = 1; i < a.size(); ++i) {
    // a < b iff ( a[i] <-> b[i] AND a[i-1:0] < b[i-1:0]) OR (~a[i] AND b[i]) 
    res = mkOr(mkAnd(mkIff(a[i], b[i]), res),
               mkAnd(mkNot(a[i]), b[i])); 
  }
  return res;
}

template <class T>
T inline sLessThanBB(const std::vector<T>&a, const std::vector<T>& b, bool orEqual) {
  Assert (a.size() && b.size());
  if (a.size() == 1) {
    if(orEqual) {
      return  mkOr(mkIff(a[0], b[0]),
                   mkAnd(a[0], mkNot(b[0]))); 
    }

    return mkAnd(a[0], mkNot(b[0]));
  }
  unsigned n = a.size() - 1; 
  std::vector<T> a1, b1;
  extractBits(a, a1, 0, n-1);
  extractBits(b, b1, 0, n-1);
  
  // unsigned comparison of the first n-1 bits
  T ures = uLessThanBB(a1, b1, orEqual);
  T res = mkOr(// a b have the same sign
               mkAnd(mkIff(a[n], b[n]),
                     ures),
               // a is negative and b positive
               mkAnd(a[n],
                     mkNot(b[n])));
  return res;
}


}
}
}

#endif
