/*********************                                                        */
/*! \file sygus_inst.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SyGuS instantiator class.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_INST_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_INST_H

#include <unordered_map>
#include <unordered_set>

#include "theory/evaluator.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {

class SygusInst : public QuantifiersModule
{
 public:
  SygusInst(QuantifiersEngine* qe);
  ~SygusInst() = default;

  /** Presolve.
   *
   * Called at the beginning of check-sat call.
   */
  // void presolve() {}
  /** Needs check.
   *
   * Returns true if this module wishes a call to be made
   * to check(e) during QuantifiersEngine::check(e).
   */
  bool needsCheck(Theory::Effort e) override;
  /** Needs model.
   *
   * Whether this module needs a model built during a
   * call to QuantifiersEngine::check(e)
   * It returns one of QEFFORT_* from quantifiers_engine.h,
   * which specifies the quantifiers effort in which it requires the model to
   * be built.
   */
  QEffort needsModel(Theory::Effort e) override;
  /** Reset.
   *
   * Called at the beginning of QuantifiersEngine::check(e).
   */
  void reset_round(Theory::Effort e) override;
  /** Check.
   *
   *   Called during QuantifiersEngine::check(e) depending
   *   if needsCheck(e) returns true.
   */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** Check complete?
   *
   * Returns false if the module's reasoning was globally incomplete
   * (e.g. "sat" must be replaced with "incomplete").
   *
   * This is called just before the quantifiers engine will return
   * with no lemmas added during a LAST_CALL effort check.
   */
  // bool checkComplete() { return true; }
  /** Check was complete for quantified formula q
   *
   * If for each quantified formula q, some module returns true for
   * checkCompleteFor( q ),
   * and no lemmas are added by the quantifiers theory, then we may answer
   * "sat", unless
   * we are incomplete for other reasons.
   */
  bool checkCompleteFor(Node q) override;
  /** Check ownership
   *
   * Called once for new quantified formulas that are registered by the
   * quantifiers theory. The primary purpose of this function is to establish
   * if this module is the owner of quantified formula q.
   */
  // void checkOwnership(Node q) {}
  /** Register quantifier
   *
   * Called once for new quantified formulas q that are pre-registered by the
   * quantifiers theory, after internal ownership of quantified formulas is
   * finalized. This does context-dependent initialization of this module.
   */
  void registerQuantifier(Node q) override;
  /** Pre-register quantifier
   *
   * Called once for new quantified formulas that are
   * pre-registered by the quantifiers theory, after
   * internal ownership of quantified formulas is finalized.
   */
  void preRegisterQuantifier(Node q) override;
  /** Assert node.
   *
   * Called when a quantified formula q is asserted to the quantifiers theory
   */
  // void assertNode(Node q) override;
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  std::string identify() const override { return "SygusInst"; }

 private:
  class InstPool
  {
   public:
    InstPool();
    ~InstPool() = default;

    /** Initialize pool with grammar 'tn'. */
    void initialize(TermDbSygus* db, TypeNode& tn);

    /** Indicates whether the enumerator finished, i.e., no new candidates can
     *  ben generated. */
    bool done();

    /** Get next enumerated term. */
    TNode next();

    /** Get all terms enumerated so far. */
    const std::vector<Node>& getTerms();

   private:
    /** Indicates whether the enumerator has finished. */
    bool d_done;
    std::unique_ptr<SygusEnumerator> d_enumerator;
    /** Enumerated terms. */
    std::vector<Node> d_terms;
    SygusStatistics d_sygus_stats;
  };

  void checkSygus(Theory::Effort e, QEffort quant_e);
  void checkDatatypes(Theory::Effort e, QEffort quant_e);

  Node getCeLiteral(Node n);

  void registerCeLemma(Node q, std::vector<TypeNode>& dtypes);

  /** Check if candidate term 't' for variable 'x' evaluates 'body' to false. */
  bool checkCandidate(TNode body,
                      TNode x,
                      TNode t,
                      std::vector<Node>& args,
                      std::vector<Node>& vals);

  Evaluator d_evaluator;

  /** Maps quantifier 'q' to the quantifiers contained in 'q'. */
  std::unordered_map<Node, std::vector<Node>, NodeHashFunction> d_quantifiers;

  /** Maps variables to their corresponding instantiation pool. */
  std::unordered_map<Node, InstPool, NodeHashFunction> d_inst_pools;

  std::unordered_map<Node, Node, NodeHashFunction> d_inst_constants;
  std::unordered_map<Node, Node, NodeHashFunction> d_var_eval;
  std::unordered_map<Node, Node, NodeHashFunction> d_ce_lits;

  // context::CDHashSet<Node, NodeHashFunction> d_added_dt_lemma;

  std::unordered_map<Node, std::unique_ptr<DecisionStrategy>, NodeHashFunction>
      d_dstrat;

  std::unordered_set<Node, NodeHashFunction> d_active_quant;
  std::unordered_set<Node, NodeHashFunction> d_inactive_quant;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
