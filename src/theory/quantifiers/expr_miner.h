/*********************                                                        */
/*! \file expr_miner.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief expr_miner
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__EXPRESSION_MINER_H
#define CVC4__THEORY__QUANTIFIERS__EXPRESSION_MINER_H

#include <map>
#include <memory>
#include <vector>

#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "expr/variable_type_map.h"
#include "smt/smt_engine.h"
#include "theory/quantifiers/sygus_sampler.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Expression miner
 *
 * This is a virtual base class for modules that "mines" certain information
 * from (enumerated) expressions. This includes:
 * - candidate rewrite rules (--sygus-rr-synth)
 */
class ExprMiner
{
 public:
  ExprMiner() : d_sampler(nullptr) {}
  virtual ~ExprMiner() {}
  /** initialize
   *
   * This initializes this expression miner. The argument vars indicates the
   * free variables of terms that will be added to this class. The argument
   * sampler gives an (optional) pointer to a sampler, which is used to
   * sample tuples of valuations of these variables.
   */
  virtual void initialize(const std::vector<Node>& vars,
                          SygusSampler* ss = nullptr);
  /** add term
   *
   * This registers term n with this expression miner. The output stream out
   * is provided as an argument for the purposes of outputting the result of
   * the expression mining done by this class. For example, candidate-rewrite
   * output is printed on out by the candidate rewrite generator miner.
   */
  virtual bool addTerm(Node n, std::ostream& out) = 0;

 protected:
  /** the set of variables used by this class */
  std::vector<Node> d_vars;
  /** pointer to the sygus sampler object we are using */
  SygusSampler* d_sampler;
  /**
   * Maps to skolems for each free variable that appears in a check. This is
   * used during initializeChecker so that query (which may contain free
   * variables) is converted to a formula without free variables.
   */
  std::map<Node, Node> d_fv_to_skolem;
  /** convert */
  Node convertToSkolem(Node n);
  /** initialize checker
   *
   * This function initializes the smt engine smte to check the satisfiability
   * of the argument "query", which is a formula whose free variables (of
   * kind BOUND_VARIABLE) are a subset of d_vars.
   */
  void initializeChecker(std::unique_ptr<SmtEngine>& smte, Node query);
  /**
   * Run the satisfiability check on query and return the result
   * (sat/unsat/unknown).
   *
   * In contrast to the above method, this call should be used for cases where
   * the model for the query is not important.
   */
  Result doCheck(Node query);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__EXPRESSION_MINER_H */
