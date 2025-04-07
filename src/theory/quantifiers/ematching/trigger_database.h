/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Trigger trie class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__TRIGGER_DATABASE_H
#define CVC5__THEORY__QUANTIFIERS__TRIGGER_DATABASE_H

#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/ematching/trigger_trie.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class QuantifiersInferenceManager;
class QuantifiersState;
class QuantifiersRegistry;
class TermRegistry;

namespace inst {

/**
 * A database of triggers, which manages how triggers are constructed.
 */
class TriggerDatabase : protected EnvObj
{
 public:
  TriggerDatabase(Env& env,
                  QuantifiersState& qs,
                  QuantifiersInferenceManager& qim,
                  QuantifiersRegistry& qr,
                  TermRegistry& tr);
  ~TriggerDatabase();

  /** mkTrigger method
   *
   * This makes an instance of a trigger object.
   * @param qe Pointer to the quantifier engine;
   * @param q The quantified formula we are making a trigger for
   * @param nodes The nodes comprising the (multi-)trigger
   * @param keepAll Don't remove unneeded patterns;
   * @param trOption Policy for dealing with triggers that already exist (see
   * below)
   * @param useNVars Number of variables that should be bound by the trigger
   * typically, the number of variables in q (0 defaults to the number of
   * variables in q).
   * @param isUser Whether this is a user trigger (for output trace).
   */
  enum
  {
    TR_MAKE_NEW,    // make new trigger even if it already may exist
    TR_GET_OLD,     // return a previous trigger if it had already been created
    TR_RETURN_NULL  // return null if a duplicate is found
  };
  Trigger* mkTrigger(Node q,
                     const std::vector<Node>& nodes,
                     bool keepAll = true,
                     int trOption = TR_MAKE_NEW,
                     size_t useNVars = 0,
                     bool isUser = false);
  /** single trigger version that calls the above function */
  Trigger* mkTrigger(Node q,
                     Node n,
                     bool keepAll = true,
                     int trOption = TR_MAKE_NEW,
                     size_t useNVars = 0,
                     bool isUser = false);

  /** make trigger terms
   *
   * This takes a set of eligible trigger terms and stores a subset of them in
   * trNodes, such that :
   *   (1) the terms in trNodes contain at least n_vars of the quantified
   *       variables in quantified formula q, and
   *   (2) the set trNodes is minimal, i.e. removing one term from trNodes
   *       always violates (1).
   */
  static bool mkTriggerTerms(Node q,
                             const std::vector<Node>& nodes,
                             size_t nvars,
                             std::vector<Node>& trNodes);

 private:
  /** The trigger trie, containing the triggers */
  TriggerTrie d_trie;
  /** Reference to the quantifiers state */
  QuantifiersState& d_qs;
  /** Reference to the quantifiers inference manager */
  QuantifiersInferenceManager& d_qim;
  /** The quantifiers registry */
  QuantifiersRegistry& d_qreg;
  /** Reference to the term registry */
  TermRegistry& d_treg;
};

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__TRIGGER_DATABASE_H */
