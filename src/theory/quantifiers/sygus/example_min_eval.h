/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for minimizing the number of calls to evaluate a term
 * on substitutions with a fixed domain.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EXAMPLE_MIN_EVAL_H
#define CVC5__THEORY__QUANTIFIERS__EXAMPLE_MIN_EVAL_H

#include <vector>

#include "expr/node.h"
#include "expr/node_trie.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * Virtual evaluator class for Example Minimize Eval.
 */
class EmeEval
{
 public:
  EmeEval() {}
  virtual ~EmeEval() {}
  /** Evaluate n given substitution { args -> vals }. */
  virtual Node eval(TNode n,
                    const std::vector<Node>& args,
                    const std::vector<Node>& vals) = 0;
};

/**
 * Example Minimize Eval
 *
 * This class is designed to evaluate a term on a set of substitutions
 * with a fixed domain.
 *
 * Its key feature is that substitutions that are identical over the free
 * variables of the term are not recomputed. For example, say I wish to evaluate
 * x+5 on substitutions having the domain { x, y }. Then, for the substitutions:
 *  { x -> 0, y -> 1 }
 *  { x -> 0, y -> 2 }
 *  { x -> 0, y -> 3 }
 *  { x -> 1, y -> 3 }
 * I would only compute the result of 0+5 once. On the other hand, evaluating
 * x+y for the above substitutions would require 4 evaluations.
 *
 * To use this class, call initialize(n,vars) first and then
 * evaluate(subs_1) ... evaluate(subs_n) as desired. Details on these methods
 * can be found below.
 */
class ExampleMinEval
{
 public:
  /**
   * Initialize this cache to evaluate n on substitutions with domain vars.
   * Argument ece is the evaluator object.
   */
  ExampleMinEval(Node n, const std::vector<Node>& vars, EmeEval* ece);
  ~ExampleMinEval() {}
  /**
   * Return the result of evaluating n * { vars -> subs } where vars is the
   * set of variables passed to initialize above.
   */
  Node evaluate(const std::vector<Node>& subs);

 private:
  /** The node to evaluate */
  Node d_evalNode;
  /** The domain of substitutions */
  std::vector<Node> d_vars;
  /** The indices in d_vars that occur free in n */
  std::vector<size_t> d_indices;
  /**
   * The trie of results. This maps subs[d_indices[0]] .. subs[d_indices[j]]
   * to the result of the evaluation. For the example at the top of this class,
   * this trie would map (0) -> 5, (1) -> 6.
   */
  NodeTrie d_trie;
  /** Pointer to the evaluator object */
  EmeEval* d_ece;
};

class TermDbSygus;

/** An example cache evaluator based on the term database sygus utility */
class EmeEvalTds : public EmeEval
{
 public:
  EmeEvalTds(TermDbSygus* tds, TypeNode tn) : d_tds(tds), d_tn(tn) {}
  virtual ~EmeEvalTds() {}
  /**
   * Evaluate n given substitution { args -> vals } using the term database
   * sygus evaluateBuiltin function.
   */
  Node eval(TNode n,
            const std::vector<Node>& args,
            const std::vector<Node>& vals) override;

 private:
  /** Pointer to the sygus term database */
  TermDbSygus* d_tds;
  /** The sygus type of the node we will be evaluating */
  TypeNode d_tn;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
