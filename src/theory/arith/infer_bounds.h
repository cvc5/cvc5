/*********************                                                        */
/*! \file infer_bounds.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
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

#include "cvc4_private.h"

#pragma once

#include <ostream>

#include "expr/node.h"
#include "theory/arith/delta_rational.h"
#include "theory/theory.h"
#include "util/integer.h"
#include "util/maybe.h"
#include "util/rational.h"


namespace CVC4 {
namespace theory {
namespace arith {

namespace inferbounds {
  enum Algorithms {None = 0, Lookup, RowSum, Simplex};
  enum SimplexParamKind { Unbounded, NumVars, Direct};

class InferBoundAlgorithm {
private:
  Algorithms d_alg;
  Maybe<int> d_simplexRounds;
  InferBoundAlgorithm(Algorithms a);
  InferBoundAlgorithm(const Maybe<int>& simplexRounds);

public:
  InferBoundAlgorithm();

  Algorithms getAlgorithm() const;
  const Maybe<int>& getSimplexRounds() const;

  static InferBoundAlgorithm mkLookup();
  static InferBoundAlgorithm mkRowSum();
  static InferBoundAlgorithm mkSimplex(const Maybe<int>& rounds);
};

std::ostream& operator<<(std::ostream& os, const Algorithms a);
} /* namespace inferbounds */

class ArithEntailmentCheckParameters
{
 private:
  typedef std::vector<inferbounds::InferBoundAlgorithm> VecInferBoundAlg;
  VecInferBoundAlg d_algorithms;

public:
  typedef VecInferBoundAlg::const_iterator const_iterator;

  ArithEntailmentCheckParameters();
  ~ArithEntailmentCheckParameters();

  void addLookupRowSumAlgorithms();
  void addAlgorithm(const inferbounds::InferBoundAlgorithm& alg);

  const_iterator begin() const;
  const_iterator end() const;
};



class InferBoundsResult {
public:
  InferBoundsResult();
  InferBoundsResult(Node term, bool ub);

  void setBound(const DeltaRational& dr, Node exp);
  bool foundBound() const;

  void setIsOptimal();
  bool boundIsOptimal() const;

  void setInconsistent();
  bool inconsistentState() const;

  const DeltaRational& getValue() const;
  bool boundIsRational() const;
  const Rational& valueAsRational() const;
  bool boundIsInteger() const;
  Integer valueAsInteger() const;

  Node getTerm() const;
  Node getLiteral() const;
  void setTerm(Node t){ d_term = t; }

  /* If there is a bound, this is a node that explains the bound. */
  Node getExplanation() const;

  bool budgetIsExhausted() const;
  void setBudgetExhausted();

  bool thresholdWasReached() const;
  void setReachedThreshold();

  bool findUpperBound() const { return d_upperBound; }

  void setFindLowerBound() { d_upperBound = false; }
  void setFindUpperBound() { d_upperBound = true; }
private:
  /* was a bound found */
  bool d_foundBound;

  /* was the budget exhausted */
  bool d_budgetExhausted;

  /* does the bound have to be optimal*/
  bool d_boundIsProvenOpt;

  /* was this started on an inconsistent state. */
  bool d_inconsistentState;

  /* reached the threshold. */
  bool d_reachedThreshold;

  /* the value of the bound */
  DeltaRational d_value;

  /* The input term. */
  Node d_term;

  /* Was the bound found an upper or lower bound.*/
  bool d_upperBound;

  /* Explanation of the bound. */
  Node d_explanation;
};

std::ostream& operator<<(std::ostream& os, const InferBoundsResult& ibr);

class ArithEntailmentCheckSideEffects
{
 public:
  ArithEntailmentCheckSideEffects();
  ~ArithEntailmentCheckSideEffects();

  InferBoundsResult& getSimplexSideEffects();

private:
  InferBoundsResult* d_simplexSideEffects;
};


} /* namespace arith */
} /* namespace theory */
} /* namespace CVC4 */
