/*********************                                                        */
/*! \file unconstrained_simplifier.h
 ** \verbatim
 ** Original author: barrett
 ** Major contributors: 
 ** Minor contributors (to current version):
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Simplifications based on unconstrained variables
 **
 ** This module implements a preprocessing phase which replaces certain "unconstrained" expressions
 ** by variables.  Based on Roberto Bruttomesso's PhD thesis.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__UNCONSTRAINED_SIMPLIFIER_H
#define __CVC4__UNCONSTRAINED_SIMPLIFIER_H

#include <vector>
#include <utility>

#include "expr/node.h"
#include "theory/theory.h"
#include "theory/substitutions.h"

namespace CVC4 {

class UnconstrainedSimplifier {

  /** number of expressions eliminated due to unconstrained simplification */
  IntStat d_numUnconstrainedElim;

  typedef std::hash_map<TNode, unsigned, TNodeHashFunction> TNodeCountMap;
  typedef std::hash_map<TNode, TNode, TNodeHashFunction> TNodeMap;
  typedef std::hash_set<TNode, TNodeHashFunction> TNodeSet;

  TNodeCountMap d_visited;
  TNodeMap d_visitedOnce;
  TNodeSet d_unconstrained;

  context::Context* d_context;
  theory::SubstitutionMap d_substitutions;

  const LogicInfo& d_logicInfo;

  void visitAll(TNode assertion);
  Node newUnconstrainedVar(TypeNode t, TNode var);
  void processUnconstrained();
  void removeExpr(TNode node);

public:
  UnconstrainedSimplifier(context::Context* context, const LogicInfo& logicInfo);
  ~UnconstrainedSimplifier();
  void processAssertions(std::vector<Node>& assertions);
};

}

#endif
