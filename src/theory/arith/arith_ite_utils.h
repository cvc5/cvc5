/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

// Pass 1: label the ite as (constant) or (+ constant variable)

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__ARITH_ITE_UTILS_H
#define CVC5__THEORY__ARITH__ARITH_ITE_UTILS_H

#include <unordered_map>

#include "context/cdinsert_hashmap.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "util/integer.h"

namespace cvc5::internal {
namespace preprocessing {
namespace util {
class ContainsTermITEVisitor;
}
}  // namespace preprocessing

namespace theory {

class SubstitutionMap;

namespace arith {

class ArithIteUtils : protected EnvObj
{
  preprocessing::util::ContainsTermITEVisitor& d_contains;
  SubstitutionMap& d_subs;

  typedef std::unordered_map<Node, Node> NodeMap;
  // cache for reduce vars
  NodeMap d_reduceVar; // if reduceVars[n].isNull(), treat reduceVars[n] == n

  // reduceVars[n] = d_constants[n] + d_varParts[n]
  NodeMap d_constants; // d_constants[n] is a constant ite tree
  NodeMap d_varParts; // d_varParts[n] is a polynomial


  NodeMap d_reduceGcd;
  typedef std::unordered_map<Node, Integer> NodeIntegerMap;
  NodeIntegerMap d_gcds;

  Integer d_one;

  context::CDO<uint64_t> d_subcount;
  typedef context::CDInsertHashMap<Node, Node> CDNodeMap;
  CDNodeMap d_skolems;

  typedef std::map<Node, std::set<Node> > ImpMap;
  ImpMap d_implies;

  std::vector<Node> d_orBinEqs;

public:
 ArithIteUtils(Env& env,
               preprocessing::util::ContainsTermITEVisitor& contains,
               SubstitutionMap& subs);
 ~ArithIteUtils();

 //(ite ?v_2 ?v_1 (ite ?v_3 (- ?v_1 128) (- ?v_1 256)))

 /** removes common sums variables sums from term ites. */
 Node reduceVariablesInItes(Node n);

 Node reduceConstantIteByGCD(Node n);

 void clear();

 Node applySubstitutions(TNode f);
 unsigned getSubCount() const;

 void learnSubstitutions(const std::vector<Node>& assertions);

private:
  /* applies this to all children of n and constructs the result */
  Node applyReduceVariablesInItes(Node n);

  const Integer& gcdIte(Node n);
  Node reduceIteConstantIteByGCD_rec(Node n, const Rational& q);
  Node reduceIteConstantIteByGCD(Node n);

  void addSubstitution(TNode f, TNode t);
  Node selectForCmp(Node n) const;

  void collectAssertions(TNode assertion);
  void addImplications(Node x, Node y);
  Node findIteCnd(TNode tb, TNode fb) const;
  bool solveBinOr(TNode binor);

}; /* class ArithIteUtils */

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__ARITH_ITE_UTILS_H */
