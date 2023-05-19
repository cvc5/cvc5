/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Trigger class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__TRIGGER_H
#define CVC5__THEORY__QUANTIFIERS__TRIGGER_H

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/inference_id.h"
#include "theory/quantifiers/inst_match.h"

namespace cvc5::internal {
namespace theory {

class Valuation;

namespace quantifiers {

class QuantifiersState;
class QuantifiersInferenceManager;
class QuantifiersRegistry;
class TermRegistry;

namespace inst {

class IMGenerator;
class InstMatchGenerator;

/** A collection of nodes representing a trigger.
 *
 * This class encapsulates all implementations of E-matching in cvc5.
 * Its primary use is as a utility of the quantifiers module InstantiationEngine
 * (see theory/quantifiers/ematching/instantiation_engine.h) which uses Trigger
 * to make appropriate calls to Instantiate::addInstantiation(...) (see
 * theory/instantiate.h) for the instantiate utility of the quantifiers engine
 * (d_quantEngine) associated with this trigger.  These calls queue
 * instantiation lemmas to the output channel of TheoryQuantifiers during a full
 * effort check.
 *
 * Concretely, a Trigger* t is used in the following way during a full effort
 * check. Assume that t is associated with quantified formula q (see field d_f).
 * We call :
 *
 * // setup initial information
 * t->resetInstantiationRound();
 * // will produce instantiations based on matching with all terms
 * t->reset( Node::null() );
 * // add all instantiations based on E-matching with this trigger and the
 * // current context
 * t->addInstantiations();
 *
 * This will result in (a set of) calls to
 * Instantiate::addInstantiation(q, m1)...Instantiate::addInstantiation(q, mn),
 * where m1...mn are InstMatch objects. These calls add the corresponding
 * instantiation lemma for (q,mi) on the output channel associated with
 * d_quantEngine.
 *
 * The Trigger class is wrapper around an underlying IMGenerator class, which
 * implements various forms of E-matching for its set of nodes (d_nodes), which
 * is refered to in the literature as a "trigger". A trigger is a set of terms
 * whose free variables are the bound variables of a quantified formula q,
 * and that is used to guide instantiations for q (for example, see "Efficient
 * E-Matching for SMT Solvers" by de Moura et al).
 *
 * For example of an instantiation lemma produced by E-matching :
 *
 * quantified formula : forall x. P( x )
 *            trigger : P( x )
 *     ground context : ~P( a )
 *
 * Then E-matching matches P( x ) and P( a ), resulting in the match { x -> a }
 * which is used to generate the instantiation lemma :
 *   (forall x. P( x )) => P( a )
 *
 * Terms that are provided as input to a Trigger class via mkTrigger
 * should be in "instantiation constant form", see
 * TermUtil::getInstConstantNode. Say we have quantified formula q whose AST is
 * the Node (FORALL (BOUND_VAR_LIST x) (NOT (P x)) (INST_PATTERN_LIST
 * (INST_PATTERN (P x)))) then TermUtil::getInstConstantNode( q, (P x) ) = (P
 * IC) where IC = TermUtil::getInstantiationConstant( q, i ). Trigger expects as
 * input (P IC) to represent the Trigger (P x). This form ensures that
 * references to bound variables are unique to quantified formulas, which is
 * required to ensure the correctness of instantiation lemmas we generate.
 *
 */
class Trigger : protected EnvObj
{
  friend class IMGenerator;

 public:
  /** trigger constructor */
  Trigger(Env& env,
          QuantifiersState& qs,
          QuantifiersInferenceManager& qim,
          QuantifiersRegistry& qr,
          TermRegistry& tr,
          Node q,
          std::vector<Node>& nodes);
  virtual ~Trigger();
  /** get the generator associated with this trigger */
  IMGenerator* getGenerator() { return d_mg; }
  /** Reset instantiation round.
   *
  * Called once at beginning of an instantiation round.
  */
  void resetInstantiationRound();
  /** Reset the trigger.
   *
  * eqc is the equivalence class from which to match ground terms. If eqc is
  * Node::null(), then we match ground terms from all equivalence classes.
  */
  void reset( Node eqc );
  /** add all available instantiations, based on the current context
  *
  * This function makes the appropriate calls to d_qe->addInstantiation(...)
  * based on the current ground terms and equalities in the current context,
  * via queries to functions in d_qe. This calls the addInstantiations function
  * of the underlying match generator. It can be extended to
  * produce instantiations beyond what is produced by the match generator
  * (for example, see theory/quantifiers/ematching/ho_trigger.h).
  */
  virtual uint64_t addInstantiations();
  /** Return whether this is a multi-trigger. */
  bool isMultiTrigger() const;
  /** Get instantiation pattern list associated with this trigger.
   *
  * An instantiation pattern list is the node representation of a trigger, in
  * particular, it is the third argument of quantified formulas which have user
  * (! ... :pattern) attributes.
  */
  Node getInstPattern() const;
  /* A heuristic value indicating how active this generator is.
   *
  * This returns the number of ground terms for the match operators in terms
  * from d_nodes. This score is only used with the experimental option
  *   --trigger-active-sel.
  */
  int getActiveScore();
  /** print debug information for the trigger */
  void debugPrint(const char* c) const;

 protected:
  /** add an instantiation (called by InstMatchGenerator)
   *
   * This calls Instantiate::addInstantiation(...) for instantiations
   * associated with m. Typically, m is associated with a single instantiation,
   * but in some cases (e.g. higher-order) we may modify m before calling
   * Instantiate::addInstantiation(...).
   */
  virtual bool sendInstantiation(std::vector<Node>& m, InferenceId id);
  /**
   * Ensure that all ground subterms of n have been preprocessed. This makes
   * calls to the provided valuation to obtain the preprocessed form of these
   * terms. The preprocessed form of each ground subterm is added to gts.
   *
   * As an optimization, this method does not preprocess terms with no
   * arguments, e.g. variables and constants are not preprocessed (as they
   * should not change after preprocessing), nor are they added to gts.
   *
   * @param val The valuation to use for looking up preprocessed terms.
   * @param n The node to process, which is in inst-constant form (free
   * variables have been substituted by corresponding INST_CONSTANT).
   * @param gts The set of preprocessed ground subterms of n.
   * @return The converted form of n where all ground subterms have been
   * replaced by their preprocessed form.
   */
  static Node ensureGroundTermPreprocessed(Valuation& val,
                                           Node n,
                                           std::vector<Node>& gts);
  /** The nodes comprising this trigger. */
  std::vector<Node> d_nodes;
  /** The nodes as a single s-expression */
  Node d_trNode;
  /**
   * The preprocessed ground terms in the nodes of the trigger, which as an
   * optimization omits variables and constant subterms. These terms are
   * important since we must ensure that the quantifier-free solvers are
   * aware of these terms. In particular, when adding instantiations for
   * a trigger P(f(a), x), we first check if f(a) is a term in the master
   * equality engine. If it is not, then we add the lemma k = f(a) where k
   * is the purification skolem for f(a). This ensures that f(a) will be
   * registered as a term in the master equality engine on the next
   * instantiation round. This is particularly important for cases where
   * P(f(a), x) is matched with P(f(b), c), where a=b in the current context.
   * This example would fail to match when f(a) is not registered.
   */
  std::vector<Node> d_groundTerms;
  /** Reference to the quantifiers state */
  QuantifiersState& d_qstate;
  /** Reference to the quantifiers inference manager */
  QuantifiersInferenceManager& d_qim;
  /** The quantifiers registry */
  QuantifiersRegistry& d_qreg;
  /** Reference to the term registry */
  TermRegistry& d_treg;
  /** The quantified formula this trigger is for. */
  Node d_quant;
  /** match generator
   *
  * This is the back-end utility that implements the underlying matching
  * algorithm associated with this trigger.
  */
  IMGenerator* d_mg;
  /**
   * An instantiation match, for building instantiation terms and doing
   * incremental entailment checking.
   */
  InstMatch d_instMatch;
}; /* class Trigger */

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__TRIGGER_H */
