/*********************                                                        */
/*! \file decision_strategy.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Base classes for decision strategies used by theory solvers
 ** for use in the DecisionManager of TheoryEngine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__DECISION_STRATEGY__H
#define CVC4__THEORY__DECISION_STRATEGY__H

#include <map>
#include "context/cdo.h"
#include "expr/node.h"
#include "theory/valuation.h"

namespace CVC4 {
namespace theory {

/**
 * Virtual base class for decision strategies.
 */
class DecisionStrategy
{
 public:
  DecisionStrategy() {}
  virtual ~DecisionStrategy() {}
  /**
   * Initalize this strategy, This is called once per satisfiability call by
   * the DecisionManager, prior to using this strategy.
   */
  virtual void initialize() = 0;
  /**
   * If this method returns a non-null node n, then n is the required next
   * decision of this strategy. It must be the case that n is a literal in
   * the current CNF stream.
   */
  virtual Node getNextDecisionRequest() = 0;
  /** identify this strategy (for debugging) */
  virtual std::string identify() const = 0;
};

/**
 * Decision strategy finite model finding.
 *
 * This is a virtual base class for decision strategies that follow the
 * "finite model finding" pattern for decisions. Such strategies have the
 * distinguishing feature that they are interested in a stream of literals
 * L_1, L_2, L_3, ... and so on. At any given time, they request that L_i is
 * asserted true for a minimal i.
 *
 * To enforce this strategy, this class maintains a SAT-context dependent
 * index d_curr_literal, which corresponds to the minimal index of a literal
 * in the above list that is not asserted false. A call to
 * getNextDecisionRequest increments this value until we find a literal L_j
 * that is not assigned false. If L_j is unassigned, we return it as a decision,
 * otherwise we return no decisions.
 */
class DecisionStrategyFmf : public DecisionStrategy
{
 public:
  DecisionStrategyFmf(context::Context* satContext, Valuation valuation);
  virtual ~DecisionStrategyFmf() {}
  /** initialize */
  void initialize() override;
  /** get next decision request */
  Node getNextDecisionRequest() override;
  /** Make the n^th literal of this strategy */
  virtual Node mkLiteral(unsigned n) = 0;
  /**
   * This method returns true iff there exists a (minimal) i such that L_i
   * is a literal allocated by this class, and is asserted true in the current
   * context. If it returns true, the argument i is set to this i.
   */
  bool getAssertedLiteralIndex(unsigned& i) const;
  /**
   * This method returns the literal L_i allocated by this class that
   * has been asserted true in the current context and is such that i is
   * minimal. It returns null if no such literals exist.
   */
  Node getAssertedLiteral();
  /** Get the n^th literal of this strategy */
  Node getLiteral(unsigned lit);

 protected:
  /**
   * The valuation of this class, used for knowing what literals are asserted,
   * and with what polarity.
   */
  Valuation d_valuation;
  /**
   * The (SAT-context-dependent) flag that is true if there exists a literal
   * of this class that is asserted true in the current context, according to
   * d_valuation.
   */
  context::CDO<bool> d_has_curr_literal;
  /**
   * The (SAT-context-dependent) index of the current literal of this strategy.
   * This corresponds to the first literal that is not asserted false in the
   * current context, according to d_valuation.
   */
  context::CDO<unsigned> d_curr_literal;
  /** the list of literals of this strategy */
  std::vector<Node> d_literals;
};

/**
 * Special case of above where we only wish to allocate a single literal L_1.
 */
class DecisionStrategySingleton : public DecisionStrategyFmf
{
 public:
  DecisionStrategySingleton(const char* name,
                            Node lit,
                            context::Context* satContext,
                            Valuation valuation);
  /**
   * Make the n^th literal of this strategy. This method returns d_literal if
   * n=0, null otherwise.
   */
  Node mkLiteral(unsigned n) override;
  /** Get single literal */
  Node getSingleLiteral();
  /** identify */
  std::string identify() const override { return d_name; }

 private:
  /** the name of this strategy */
  std::string d_name;
  /** the literal to decide on */
  Node d_literal;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__DECISION_STRATEGY__H */
