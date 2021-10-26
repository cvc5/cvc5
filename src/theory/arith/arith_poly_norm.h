/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic utility for polynomial normalization
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__POLY_NORM_H
#define CVC5__THEORY__ARITH__POLY_NORM_H

#include <unordered_map>

#include "expr/node.h"

namespace cvc5 {
namespace theory {
namespace arith {

class MonomialVar
{
public:
  static Node multMonoVar(Node m1, Node m2);
};

class PolyNorm
{
 public:
  void addMonomial(Node x, Node c, bool isNeg = false);
  void multiplyMonomial(Node x, Node c);
  void add(const PolyNorm& p);
  void subtract(const PolyNorm& p);
  void multiply(const PolyNorm& p);
  void clear();
  bool empty() const;

  std::unordered_map<Node, Node> d_polyNorm;
  
  static PolyNorm mkPolyNorm(Node n);
  
  static bool isArithPolyNorm(Node a, Node b);
};

}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__ARITH__POLY_NORM_H */
