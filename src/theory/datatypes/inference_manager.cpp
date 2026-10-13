/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Datatypes inference manager.
 */

#include "theory/datatypes/inference_manager.h"

#include "expr/dtype.h"
#include "options/datatypes_options.h"
#include "proof/eager_proof_generator.h"
#include "theory/datatypes/theory_datatypes.h"
#include "theory/rewriter.h"
#include "theory/theory.h"
#include "theory/theory_state.h"
#include "theory/trust_substitutions.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace datatypes {

InferenceManager::InferenceManager(Env& env,
                                   TheoryDatatypes& t,
                                   TheoryState& state)
    : InferenceManagerBuffered(env, t, state, "theory::datatypes::"),
      d_dt(t),
      d_ipc(isProofEnabled() ? new InferProofCons(env, context()) : nullptr),
      d_lemPg(isProofEnabled() ? new EagerProofGenerator(
                                     env, userContext(), "datatypes::lemPg")
                               : nullptr)
{
  d_false = nodeManager()->mkConst(false);
}

InferenceManager::~InferenceManager() {}

void InferenceManager::addPendingInference(Node conc,
                                           InferenceId id,
                                           Node exp,
                                           bool forceLemma)
{
  Trace("dt-im") << "Pending inference: " << conc << " / " << exp << " / " << id
                 << std::endl;
  // if we are forcing the inference to be processed as a lemma, if the
  // dtInferAsLemmas option is set, or if the inference must be sent as a lemma
  // based on the policy in mustCommunicateFact.
  if (forceLemma || options().datatypes.dtInferAsLemmas
      || DatatypesInference::mustCommunicateFact(conc, exp))
  {
    d_pendingLem.emplace_back(new DatatypesInference(this, conc, exp, id));
  }
  else
  {
    d_pendingFact.emplace_back(new DatatypesInference(this, conc, exp, id));
  }
}

void InferenceManager::process()
{
  // if we are in conflict, immediately reset and clear pending
  if (d_theoryState.isInConflict())
  {
    reset();
    clearPending();
    return;
  }
  // process pending lemmas, used infrequently, only for definitional lemmas
  doPendingLemmas();
  // now process the pending facts
  doPendingFacts();
}

bool InferenceManager::sendDtLemma(Node lem, InferenceId id, LemmaProperty p)
{
  if (isProofEnabled())
  {
    TrustNode trn = processDtLemma(lem, Node::null(), id);
    return trustedLemma(trn, id);
  }
  // otherwise send as a normal lemma directly
  return lemma(lem, id, p);
}

void InferenceManager::sendDtConflict(const std::vector<Node>& conf,
                                      InferenceId id)
{
  if (isProofEnabled())
  {
    Node exp = nodeManager()->mkAnd(conf);
    prepareDtInference(d_false, exp, id, d_ipc.get());
  }
  conflictExp(id, conf, d_ipc.get());
}

TrustNode InferenceManager::processDtLemma(Node conc, Node exp, InferenceId id)
{
  // set up a proof constructor
  std::shared_ptr<InferProofCons> ipcl;
  if (isProofEnabled())
  {
    ipcl = std::make_shared<InferProofCons>(d_env, nullptr);
  }
  conc = prepareDtInference(conc, exp, id, ipcl.get());
  // send it as a lemma
  Node lem;
  if (!exp.isNull() && !exp.isConst())
  {
    lem = nodeManager()->mkNode(Kind::IMPLIES, exp, conc);
  }
  else
  {
    lem = conc;
  }
  if (isProofEnabled())
  {
    // store its proof
    std::shared_ptr<ProofNode> pbody = ipcl->getProofFor(conc);
    std::shared_ptr<ProofNode> pn = pbody;
    if (!exp.isNull() && !exp.isConst())
    {
      std::vector<Node> expv;
      expv.push_back(exp);
      pn = d_env.getProofNodeManager()->mkScope(pbody, expv);
    }
    d_lemPg->setProofFor(lem, pn);
  }
  return TrustNode::mkTrustLemma(lem, d_lemPg.get());
}

Node InferenceManager::processDtFact(Node conc,
                                     Node exp,
                                     InferenceId id,
                                     ProofGenerator*& pg)
{
  pg = d_ipc.get();
  return prepareDtInference(conc, exp, id, d_ipc.get());
}

Node InferenceManager::prepareDtInference(Node conc,
                                          Node exp,
                                          InferenceId id,
                                          InferProofCons* ipc)
{
  Trace("dt-lemma-debug") << "prepareDtInference : " << conc << " via " << exp
                          << " by " << id << std::endl;
  if (id == InferenceId::DATATYPES_INST)
  {
    // Mark the equivalence class as instantiated. Note this method is the
    // single point through which all datatypes inferences pass when they are
    // sent, either as a lemma (processDtLemma) or as an internal fact
    // (processDtFact). Marking the equivalence class here, and not when the
    // inference was computed, guarantees that it is marked as instantiated if
    // and only if the inference of the instantiate rule was sent. In
    // particular, if the inference is discarded while still pending, e.g. when
    // a conflict is raised, then the equivalence class is left unmarked and we
    // will apply the instantiate rule to it again. See issue #12794.
    Assert(conc.getKind() == Kind::EQUAL);
    d_dt.notifyInstantiate(conc[0]);
  }
  if (isProofEnabled())
  {
    Assert(ipc != nullptr);
    // If proofs are enabled, notify the proof constructor.
    // Notice that we have to reconstruct a datatypes inference here. This is
    // because the inference in the pending vector may be destroyed as we are
    // processing this inference, if we triggered to backtrack based on the
    // call below, since it is a unique pointer.
    std::shared_ptr<DatatypesInference> di =
        std::make_shared<DatatypesInference>(this, conc, exp, id);
    ipc->notifyFact(di);
  }
  return conc;
}

}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5::internal
