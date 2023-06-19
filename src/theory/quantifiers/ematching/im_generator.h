/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Clark Barrett
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inst match generator base class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__IM_GENERATOR_H
#define CVC5__THEORY__QUANTIFIERS__IM_GENERATOR_H

#include <map>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/inference_id.h"
#include "theory/quantifiers/inst_match.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class QuantifiersState;
class TermRegistry;

namespace inst {

class Trigger;

/** IMGenerator class
 *
 * Virtual base class for generating InstMatch objects, which correspond to
 * quantifier instantiations. The main use of this class is as a backend utility
 * to Trigger (see theory/quantifiers/ematching/trigger.h).
 *
 * Some functions below take as argument a pointer to the current quantifiers
 * engine, which is used for making various queries about what terms and
 * equalities exist in the current context.
 *
 * Some functions below take a pointer to a parent Trigger object, which is used
 * to post-process and finalize the instantiations through
 * sendInstantiation(...), where the parent trigger will make calls to
 * Instantiate::addInstantiation(...). The latter function is the entry
 * point in which instantiate lemmas are enqueued to be sent on the output
 * channel.
 */
class IMGenerator : protected EnvObj
{
 public:
  IMGenerator(Env& env, Trigger* tparent);
  virtual ~IMGenerator() {}
  /** Reset instantiation round.
   *
   * Called once at beginning of an instantiation round.
   */
  virtual void resetInstantiationRound() {}
  /** Reset.
   *
   * eqc is the equivalence class to search in (any if eqc=null).
   * Returns true if this generator can produce instantiations, and false
   * otherwise. An example of when it returns false is if it can be determined
   * that no appropriate matchable terms occur based on eqc.
   */
  virtual bool reset(Node eqc) { return true; }
  /** Get the next match.
   *
   * Must call reset( eqc ) before this function. This constructs an
   * instantiation, which it populates in data structure m,
   * based on the current context using the implemented matching algorithm.
   *
   * @param m the InstMatch object we are generating
   * @return a value >0 if an instantiation was successfully generated
   */
  virtual int getNextMatch(InstMatch& m) { return 0; }
  /** add instantiations
   *
   * This adds all available instantiations for the quantified formula of m
   * based on the current context using the implemented matching algorithm. It
   * typically is implemented as a fixed point of getNextMatch above.
   *
   * It returns the number of instantiations added using calls to
   * Instantiate::addInstantiation(...).
   */
  virtual uint64_t addInstantiations(InstMatch& m) { return 0; }
  /** get active score
   *
   * A heuristic value indicating how active this generator is.
   */
  virtual int getActiveScore() { return 0; }

 protected:
  /** send instantiation
   *
   * This method sends instantiation, specified by terms, to the parent trigger
   * object, which will in turn make a call to
   * Instantiate::addInstantiation(...). This method returns true if a
   * call to Instantiate::addInstantiation(...) was successfully made,
   * indicating that an instantiation was enqueued in the quantifier engine's
   * lemma cache.
   */
  bool sendInstantiation(std::vector<Node>& terms, InferenceId id);
  /** The parent trigger that owns this */
  Trigger* d_tparent;
  /** Reference to the state of the quantifiers engine */
  QuantifiersState& d_qstate;
  /** Reference to the term registry */
  TermRegistry& d_treg;
}; /* class IMGenerator */

}  // namespace inst
}
}
}  // namespace cvc5::internal

#endif
