/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * State for congruence closure with free variables
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CCFV__STATE_H
#define CVC5__THEORY__QUANTIFIERS__CCFV__STATE_H

#include <memory>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/ieval/free_var_info.h"
#include "theory/quantifiers/ieval/pattern_term_info.h"
#include "theory/quantifiers/ieval/quant_info.h"

namespace cvc5::internal {

namespace expr {
class TermCanonize;
}

namespace theory {
namespace quantifiers {

class QuantifiersState;
class TermDb;

namespace ieval {

class State : protected EnvObj
{
  using NodeList = context::CDList<Node>;
  using NodeSet = context::CDHashSet<Node>;
  using NodeBoolMap = context::CDHashMap<Node, bool>;
  using NodePatTermInfoMap = context::CDHashMap<Node, std::unique_ptr<PatTermInfo>>;

 public:
  State(Env& env, context::Context* c, QuantifiersState& qs, TermDb* tdb);

  /** Watch quantified formula with the given body */
  void watch(Node q, const std::vector<Node>& vars, Node body);

  /** Assign variable */
  bool assignVar(TNode v, TNode s, std::vector<Node>& assignedQuants);

  //---------------quantifiers info
  /** Get quantifiers info */
  QuantInfo& getQuantInfo(TNode q);
  //---------------free variable info
  /** Get free variable info */
  FreeVarInfo& getOrMkFreeVarInfo(TNode v);
  FreeVarInfo& getFreeVarInfo(TNode v);
  //---------------pattern term info
  /** Get pattern term info */
  PatTermInfo& getOrMkPatTermInfo(TNode p);
  PatTermInfo& getPatTermInfo(TNode p);
  //---------------queries
  /** Is finished */
  bool isFinished() const;
  /**
   * Get value for pattern or ordinary term p. This is either a ground
   * represenative, or the none, or the null node if p is active.
   */
  TNode getValue(TNode p) const;
  /** Get none node */
  Node getNone() const;
  /** Is none */
  bool isNone(TNode n) const;
  /** Get some node */
  Node getSome() const;
  /** Is some */
  bool isSome(TNode n) const;
  /** Is ground eqc? */
  bool isGroundEqc(TNode r) const;
  /** Get the ground representative */
  TNode getGroundRepresentative(TNode n) const;
  /** Get representative */  // TODO: configurable equality engine here?
  // Node getRepresentative(Node n);
  /** Are disequal? */
  bool areDisequal(TNode a, TNode b) const;
  /** Invoke the rewriter for term n */
  Node doRewrite(Node n);
  /** Is quantifier active? */
  bool isQuantActive(TNode q) const;
  /** Set quantified formula active / inactive */
  void setQuantInactive(QuantInfo& qi);

  /** debugging */
  std::string toString() const;
  std::string toStringSearch() const;
  std::string toStringDebugSearch() const;

 private:
  //---------------equality notifications
  /**
   * Called when we have determined that pattern p will not merge with any
   * ground equivalence class.
   */
  void notifyPatternNone(TNode p);
  /**
   * Called when it is determined what pattern p is equal to.
   *
   * If g is not none, then g is the (ground) equivalence class that pattern p
   * is equal to. If g is none, then we have determined that p will *never*
   * merge into a ground equivalence class in this context.
   */
  void notifyPatternEqGround(TNode p, TNode g);
  /**
   * Notify quantified formula.
   *
   * Called when a constraint term p of quantified formula q has been assigned
   * the value val.
   */
  void notifyQuant(TNode q, TNode p, TNode val);
  /** The context, managed by the parent inst evaluator */
  context::Context* d_ctx;
  /** Quantifiers state */
  QuantifiersState& d_qstate;
  /** Term database */
  TermDb* d_tdb;
  /** Map quantified formulas to their info */
  std::map<Node, QuantInfo> d_quantInfo;
  /** Free variable info */
  std::map<Node, FreeVarInfo> d_fvInfo;
  /** Pattern term info */
  std::map<Node, PatTermInfo> d_pInfo;
  /** The none node */
  Node d_none;
  /** The some node */
  Node d_some;
  /** common constants */
  Node d_true;
  Node d_false;
  /** The terms we have set up notifications for */
  NodeSet d_registeredTerms;
  /** total number of alive quantified formulas */
  context::CDO<size_t> d_numActiveQuant;
};

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
