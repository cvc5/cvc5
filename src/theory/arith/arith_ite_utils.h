/*********************                                                        */
/*! \file arith_ite_utils.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Mathias Preiner, Aina Niemetz
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

// Pass 1: label the ite as (constant) or (+ constant variable)

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__ARITH_ITE_UTILS_H
#define CVC4__THEORY__ARITH__ARITH_ITE_UTILS_H

#include <unordered_map>

#include "expr/node.h"
#include "context/cdo.h"
#include "context/cdinsert_hashmap.h"

namespace CVC4 {
namespace preprocessing {
namespace util {
class ContainsTermITEVisitor;
}
}  // namespace preprocessing

namespace theory {

class SubstitutionMap;
class TheoryModel;

namespace arith {

class ArithIteUtils {
  preprocessing::util::ContainsTermITEVisitor& d_contains;
  SubstitutionMap* d_subs;
  TheoryModel* d_model;

  typedef std::unordered_map<Node, Node, NodeHashFunction> NodeMap;
  // cache for reduce vars
  NodeMap d_reduceVar; // if reduceVars[n].isNull(), treat reduceVars[n] == n

  // reduceVars[n] = d_constants[n] + d_varParts[n]
  NodeMap d_constants; // d_constants[n] is a constant ite tree
  NodeMap d_varParts; // d_varParts[n] is a polynomial


  NodeMap d_reduceGcd;
  typedef std::unordered_map<Node, Integer, NodeHashFunction> NodeIntegerMap;
  NodeIntegerMap d_gcds;

  Integer d_one;

  context::CDO<unsigned> d_subcount;
  typedef context::CDInsertHashMap<Node, Node, NodeHashFunction> CDNodeMap;
  CDNodeMap d_skolems;

  typedef std::map<Node, std::set<Node> > ImpMap;
  ImpMap d_implies;

  std::vector<Node> d_orBinEqs;

public:
 ArithIteUtils(preprocessing::util::ContainsTermITEVisitor& contains,
               context::Context* userContext,
               TheoryModel* model);
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

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__ARITH__ARITH_ITE_UTILS_H */
