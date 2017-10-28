/*********************                                                        */
/*! \file bv_inverter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief inverse rules for bit-vector operators
 **/

#include "cvc4_private.h"

#ifndef __CVC4__BV_INVERTER_H
#define __CVC4__BV_INVERTER_H

#include <map>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

// virtual class for model queries
class BvInverterModelQuery {
 public:
  BvInverterModelQuery() {}
  ~BvInverterModelQuery() {}
  virtual Node getModelValue(Node n) = 0;
};

// class for storing information about the solved status
class BvInverterStatus {
 public:
  BvInverterStatus() : d_status(0) {}
  ~BvInverterStatus() {}
  int d_status;
  // TODO : may not need this (conditions now appear explicitly in solved
  // forms) side conditions
  std::vector<Node> d_conds;
};

// inverter class
// TODO : move to theory/bv/ if generally useful?
class BvInverter {
 public:
  BvInverter() {}
  ~BvInverter() {}

  /** get dummy fresh variable of type tn, used as argument for sv */
  Node getSolveVariable(TypeNode tn);

  /** get inversion node, if :
   *
   *   f = getInversionSkolemFunctionFor( tn )
   *
   * This returns f( cond ).
   */
  Node getInversionNode(Node cond, TypeNode tn);

  /** Get path to pv in lit, replace that occurrence by sv and all others by
   * pvs. If return value R is non-null, then : lit.path = pv R.path = sv
   *   R.path' = pvs for all lit.path' = pv, where path' != path
   */
  Node getPathToPv(Node lit, Node pv, Node sv, Node pvs,
                   std::vector<unsigned>& path);

  /** eliminate skolem functions in node n
   *
   * This eliminates all Skolem functions from Node n and replaces them with
   * finalized Skolem variables.
   *
   * For each skolem variable we introduce, we ensure its associated side
   * condition is added to side_conditions.
   *
   * Apart from Skolem functions, all subterms of n should be eligible for
   * instantiation.
   */
  Node eliminateSkolemFunctions(TNode n, std::vector<Node>& side_conditions);

  /** solve_bv_lit
   * solve for sv in lit, where lit.path = sv
   * status accumulates side conditions
   */
  Node solve_bv_lit(Node sv, Node lit, std::vector<unsigned>& path,
                    BvInverterModelQuery* m, BvInverterStatus& status);

 private:
  /** dummy variables for each type */
  std::map<TypeNode, Node> d_solve_var;

  /** stores the inversion skolems, for each condition */
  std::unordered_map<Node, Node, NodeHashFunction> d_inversion_skolem_cache;

  /** helper function for getPathToPv */
  Node getPathToPv(Node lit, Node pv, Node sv, std::vector<unsigned>& path,
                   std::unordered_set<TNode, TNodeHashFunction>& visited);

  // is operator k invertible?
  bool isInvertible(Kind k, unsigned index);

  /** get inversion skolem for condition
   * precondition : exists x. cond( x ) is a tautology in BV,
   *               where x is getSolveVariable( tn ).
   * returns fresh skolem k of type tn, where we may assume cond( k ).
   */
  Node getInversionSkolemFor(Node cond, TypeNode tn);

  /** get inversion skolem function for type tn.
   *   This is a function of type ( Bool -> tn ) that is used for explicitly
   * storing side conditions inside terms. For all ( cond, tn ), if :
   *
   *   f = getInversionSkolemFunctionFor( tn )
   *   k = getInversionSkolemFor( cond, tn )
   *   then:
   *   f( cond ) is a placeholder for k.
   *
   * In the call eliminateSkolemFunctions, we replace all f( cond ) with k and
   * add cond{ x -> k } to side_conditions. The advantage is that f( cond )
   * explicitly contains the side condition so it automatically updates with
   * substitutions.
   */
  Node getInversionSkolemFunctionFor(TypeNode tn);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__BV_INVERTER_H */
