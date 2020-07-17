/*********************                                                        */
/*! \file word.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

/*
 * word.cpp
 *
 *  Created on: Jul 13, 2012
 *      Author: dejan
 */

#include "word.h"

#include <vector>

#include <cvc4/cvc4.h>
#include <cvc4/expr/expr_iomanip.h>
#include <cvc4/options/language.h>
#include <cvc4/options/options.h>

using namespace std;
using namespace hashsmt;
using namespace CVC4;
using namespace CVC4::options;

Expr Word::extendToSize(unsigned newSize) const {
  if (newSize <= size()) {
    return d_expr;
  } else {
    // 0-extend to size
    Expr extendOp = em()->mkConst(BitVectorZeroExtend(newSize - size()));
    return em()->mkExpr(extendOp, d_expr);
  }
}

ExprManager* Word::s_manager = 0;

ExprManager* Word::em() {
  if (s_manager == 0) {
    CVC4::Options options;
    options.setInputLanguage(language::input::LANG_SMTLIB_V2);
    options.setOutputLanguage(language::output::LANG_SMTLIB_V2);
    s_manager = new CVC4::ExprManager(options);
  }
  return s_manager;
}

Expr Word::operator == (const Word& b) const {
  return em()->mkExpr(kind::EQUAL, d_expr, b.getExpr());
}

Word Word::concat(const Word words[], unsigned size) {
  Expr concat = words[0].d_expr;
  for(unsigned i = 1; i < size; ++i) {
      concat = em()->mkExpr(kind::BITVECTOR_CONCAT, concat, words[i].d_expr);
  }
  return Word(concat);
}

void Word::print(ostream& out) const {
  out << CVC4::expr::ExprSetDepth(-1) << d_expr;
}

Word::Word(unsigned newSize, unsigned value) {
  d_expr = em()->mkConst(BitVector(newSize, value));
};

Word::Word(unsigned newSize, string name) {
  d_expr = em()->mkVar(name, em()->mkBitVectorType(newSize));
};

Word& Word::operator = (const Word& b) {
  d_expr = b.d_expr;
  return *this;
}

Word Word::operator + (const Word& b) const {
  unsigned newSize = std::max(size(), b.size());
  Expr lhs = extendToSize(newSize);
  Expr rhs = b.extendToSize(newSize);
  return em()->mkExpr(kind::BITVECTOR_PLUS, lhs, rhs);
}

Word& Word::operator += (const Word& b) {
  (*this) = (*this) + b;
  return (*this);
}

Word Word::operator ~ () const {
  return em()->mkExpr(kind::BITVECTOR_NOT, d_expr);
}

Word Word::operator & (const Word& b) const {
  unsigned newSize = std::max(size(), b.size());
  Expr lhs = extendToSize(newSize);
  Expr rhs = b.extendToSize(newSize);
  return em()->mkExpr(kind::BITVECTOR_AND, lhs, rhs);
}

Word Word::operator | (const Word& b) const {
  unsigned newSize = std::max(size(), b.size());
  Expr lhs = extendToSize(newSize);
  Expr rhs = b.extendToSize(newSize);
  return em()->mkExpr(kind::BITVECTOR_OR, lhs, rhs);
}

Word& Word::operator |= (const Word& b) {
  (*this) = (*this) | b;
  return (*this);
}

Word Word::operator ^ (const Word& b) const {
  unsigned newSize = std::max(size(), b.size());
  Expr lhs = extendToSize(newSize);
  Expr rhs = b.extendToSize(newSize);
  return em()->mkExpr(kind::BITVECTOR_XOR, lhs, rhs);
}

Word Word::operator << (unsigned amount) const {
  // Instead of shifting we just add zeroes, to ensure that ((char)x << 24) return 32 bits
  Word padding(amount, 0);
  return em()->mkExpr(kind::BITVECTOR_CONCAT, d_expr, padding.d_expr);
}

Word Word::operator >> (unsigned amount) const {
  Word shiftAmount(size(), amount);
  return em()->mkExpr(kind::BITVECTOR_LSHR, d_expr, shiftAmount.d_expr);
}

unsigned Word::size() const {
  BitVectorType type = d_expr.getType();
  return type.getSize();
}

cvc4_uint32::cvc4_uint32(const Word& b) {
  if (b.size() > 32) {
    // Extract the first 32 bits
    Expr extractOp = em()->mkConst(BitVectorExtract(31, 0));
    d_expr = em()->mkExpr(extractOp, b.getExpr());
  } else if (b.size() < 32) {
    // 0-extend to 32 bits
    Expr extendOp = em()->mkConst(BitVectorZeroExtend(32 - b.size()));
    d_expr = em()->mkExpr(extendOp, b.getExpr());    
  } else {
    d_expr = b.getExpr();
  }
}

cvc4_uchar8::cvc4_uchar8(const Word& b) {
  if (b.size() > 8) {
    // Extract the first 8 bits
    Expr extractOp = em()->mkConst(BitVectorExtract(7, 0));
    d_expr = em()->mkExpr(extractOp, b.getExpr());
  } else if (b.size() < 8) {
    // 0-extend to 8 bits
    Expr extendOp = em()->mkConst(BitVectorZeroExtend(8 - b.size()));
    d_expr = em()->mkExpr(extendOp, b.getExpr());    
  } else {
    d_expr = b.getExpr();
  }
}
