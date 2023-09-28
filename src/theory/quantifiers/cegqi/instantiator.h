/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Instantiator for counterexample-guided quantifier instantiation.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__INSTANTIATOR_H
#define CVC5__THEORY__QUANTIFIERS__INSTANTIATOR_H

#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/cegqi/ceg_instantiator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class CegInstanatior;

/** Instantiator class
 *
 * This is a virtual class that is used for methods for constructing
 * substitutions for individual variables in counterexample-guided
 * instantiation techniques.
 *
 * This class contains a set of interface functions below, which are called
 * based on a fixed instantiation method implemented by CegInstantiator.
 * In these calls, the Instantiator in turn makes calls to methods in
 * CegInstanatior (primarily constructInstantiationInc).
 */
class Instantiator : protected EnvObj
{
 public:
  Instantiator(Env& env, TypeNode tn);
  virtual ~Instantiator() {}
  /** reset
   * This is called once, prior to any of the below methods are called.
   * This function sets up any initial information necessary for constructing
   * instantiations for pv based on the current context.
   */
  virtual void reset(CegInstantiator* ci,
                     SolvedForm& sf,
                     Node pv,
                     CegInstEffort effort)
  {
  }

  /** has process equal term
   *
   * Whether this instantiator implements processEqualTerm and
   * processEqualTerms.
   */
  virtual bool hasProcessEqualTerm(CegInstantiator* ci,
                                   SolvedForm& sf,
                                   Node pv,
                                   CegInstEffort effort)
  {
    return false;
  }
  /** process equal term
   *
   * This method is called when the entailment:
   *   E |= pv_prop.getModifiedTerm(pv) = n
   * holds in the current context E, and n is eligible for instantiation.
   *
   * Returns true if an instantiation was successfully added via a call to
   * CegInstantiator::constructInstantiationInc.
   */
  virtual bool processEqualTerm(CegInstantiator* ci,
                                SolvedForm& sf,
                                Node pv,
                                TermProperties& pv_prop,
                                Node n,
                                CegInstEffort effort);
  /** process equal terms
   *
   * This method is called after process equal term, where eqc is the list of
   * eligible terms in the equivalence class of pv.
   *
   * Returns true if an instantiation was successfully added via a call to
   * CegInstantiator::constructInstantiationInc.
   */
  virtual bool processEqualTerms(CegInstantiator* ci,
                                 SolvedForm& sf,
                                 Node pv,
                                 std::vector<Node>& eqc,
                                 CegInstEffort effort)
  {
    return false;
  }

  /** whether the instantiator implements processEquality */
  virtual bool hasProcessEquality(CegInstantiator* ci,
                                  SolvedForm& sf,
                                  Node pv,
                                  CegInstEffort effort)
  {
    return false;
  }
  /** process equality
   *  The input is such that term_props.size() = terms.size() = 2
   *  This method is called when the entailment:
   *    E ^ term_props[0].getModifiedTerm(x0) =
   *    terms[0] ^ term_props[1].getModifiedTerm(x1) = terms[1] |= x0 = x1
   *  holds in current context E for fresh variables xi, terms[i] are eligible,
   *  and at least one terms[i] contains pv for i = 0,1.
   *  Notice in the basic case, E |= terms[0] = terms[1].
   *
   *  Returns true if an instantiation was successfully added via a call to
   *  CegInstantiator::constructInstantiationInc.
   */
  virtual bool processEquality(CegInstantiator* ci,
                               SolvedForm& sf,
                               Node pv,
                               std::vector<TermProperties>& term_props,
                               std::vector<Node>& terms,
                               CegInstEffort effort)
  {
    return false;
  }

  /** whether the instantiator implements processAssertion for any literal */
  virtual bool hasProcessAssertion(CegInstantiator* ci,
                                   SolvedForm& sf,
                                   Node pv,
                                   CegInstEffort effort)
  {
    return false;
  }
  /** has process assertion
  *
  * This method is called when the entailment:
  *   E |= lit
  * holds in current context E. Typically, lit belongs to the list of current
  * assertions.
  *
  * This method is used to determine whether the instantiator implements
  * processAssertion for literal lit.
  *   If this method returns null, then this intantiator does not handle the
  *   literal lit. Otherwise, this method returns a literal lit' such that:
  *   (1) lit' is true in the current model,
  *   (2) lit' implies lit.
  *   where typically lit' = lit.
  */
  virtual Node hasProcessAssertion(CegInstantiator* ci,
                                   SolvedForm& sf,
                                   Node pv,
                                   Node lit,
                                   CegInstEffort effort)
  {
    return Node::null();
  }
  /** process assertion
   * This method processes the assertion slit for variable pv.
   * lit : the substituted form (under sf) of a literal returned by
   *       hasProcessAssertion
   * alit : the asserted literal, given as input to hasProcessAssertion
   *
   *  Returns true if an instantiation was successfully added via a call to
   *  CegInstantiator::constructInstantiationInc.
   */
  virtual bool processAssertion(CegInstantiator* ci,
                                SolvedForm& sf,
                                Node pv,
                                Node lit,
                                Node alit,
                                CegInstEffort effort)
  {
    return false;
  }
  /** process assertions
   *
   * Called after processAssertion is called for each literal asserted to the
   * instantiator.
   *
   * Returns true if an instantiation was successfully added via a call to
   * CegInstantiator::constructInstantiationInc.
   */
  virtual bool processAssertions(CegInstantiator* ci,
                                 SolvedForm& sf,
                                 Node pv,
                                 CegInstEffort effort)
  {
    return false;
  }

  /** do we use the model value as instantiation for pv?
   * This method returns true if we use model value instantiations
   * at the same effort level as those determined by this instantiator.
   */
  virtual bool useModelValue(CegInstantiator* ci,
                             SolvedForm& sf,
                             Node pv,
                             CegInstEffort effort)
  {
    return effort > CEG_INST_EFFORT_STANDARD;
  }
  /** do we allow the model value as instantiation for pv? */
  virtual bool allowModelValue(CegInstantiator* ci,
                               SolvedForm& sf,
                               Node pv,
                               CegInstEffort effort)
  {
    return d_closed_enum_type;
  }

  /** do we need to postprocess the solved form for pv? */
  virtual bool needsPostProcessInstantiationForVariable(CegInstantiator* ci,
                                                        SolvedForm& sf,
                                                        Node pv,
                                                        CegInstEffort effort)
  {
    return false;
  }
  /** postprocess the solved form for pv
   *
   * This method returns true if we successfully postprocessed the solved form.
   * lemmas is a set of lemmas we wish to return along with the instantiation.
   */
  virtual bool postProcessInstantiationForVariable(CegInstantiator* ci,
                                                   SolvedForm& sf,
                                                   Node pv,
                                                   CegInstEffort effort)
  {
    return true;
  }

  /** Identify this module (for debugging) */
  virtual std::string identify() const { return "Default"; }
 protected:
  /** the type of the variable we are instantiating */
  TypeNode d_type;
  /** whether d_type is a closed enumerable type */
  bool d_closed_enum_type;
};

class ModelValueInstantiator : public Instantiator {
public:
 ModelValueInstantiator(Env& env, TypeNode tn) : Instantiator(env, tn) {}
 virtual ~ModelValueInstantiator() {}
 bool useModelValue(CegInstantiator* ci,
                    SolvedForm& sf,
                    Node pv,
                    CegInstEffort effort) override
 {
   return true;
 }
  std::string identify() const override { return "ModelValue"; }
};

/** instantiator preprocess
 *
 * This class implements techniques for preprocessing the counterexample lemma
 * generated for counterexample-guided quantifier instantiation.
 */
class InstantiatorPreprocess
{
 public:
  InstantiatorPreprocess() {}
  virtual ~InstantiatorPreprocess() {}
  /** register counterexample lemma
   * This implements theory-specific preprocessing and registration
   * of counterexample lemmas, with the same contract as
   * CegInstantiation::registerCounterexampleLemma.
   */
  virtual void registerCounterexampleLemma(Node lem,
                                           std::vector<Node>& ceVars,
                                           std::vector<Node>& auxLems)
  {
  }
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
