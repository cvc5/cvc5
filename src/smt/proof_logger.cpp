/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof logger utility.
 */

#include "smt/proof_logger.h"

#include "proof/proof.h"
#include "proof/proof_node_manager.h"
#include "smt/proof_manager.h"

namespace cvc5::internal {

ProofLoggerCpc::ProofLoggerCpc(Env& env,
                               std::ostream& out,
                               smt::PfManager* pm,
                               smt::Assertions& as)
    : ProofLogger(env),
      d_pm(pm),
      d_pnm(pm->getProofNodeManager()),
      d_as(as),
      d_atp(nodeManager()),
      // we use thresh 1 since terms may come incrementally and would benefit
      // from previous eager letification
      d_eop(env, d_atp, pm->getRewriteDatabase(), 1),
      d_eout(out, d_eop.getLetBinding(), "@t", false),
      d_ppLogged(false),
      d_numLemmasPrinted(0)
{
  Trace("pf-log-debug") << "Make proof logger" << std::endl;
  // global options on out
  options::ioutils::applyOutputLanguage(out, Language::LANG_SMTLIB_V2_6);
  options::ioutils::applyPrintArithLitToken(out, true);
  options::ioutils::applyPrintSkolemDefinitions(out, true);
}

ProofLoggerCpc::~ProofLoggerCpc() {}

void ProofLoggerCpc::logCnfPreprocessInputs(const std::vector<Node>& inputs)
{
  d_eout.getOStream() << "; log start" << std::endl;
  Trace("pf-log") << "; log: cnf preprocess input proof start" << std::endl;
  CDProof cdp(d_env);
  Node conc = nodeManager()->mkAnd(inputs);
  cdp.addTrustedStep(conc, TrustId::PREPROCESSED_INPUT, inputs, {});
  std::shared_ptr<ProofNode> pfn = cdp.getProofFor(conc);
  ProofScopeMode m = ProofScopeMode::DEFINITIONS_AND_ASSERTIONS;
  d_ppProof = d_pm->connectProofToAssertions(pfn, d_as, m);
  d_eop.print(d_eout, d_ppProof, m);
  printPendingLemmas();
  Trace("pf-log") << "; log: cnf preprocess input proof end" << std::endl;
}

void ProofLoggerCpc::logCnfPreprocessInputProofs(
    std::vector<std::shared_ptr<ProofNode>>& pfns)
{
  Trace("pf-log") << "; log: cnf preprocess input proof start" << std::endl;
  // if the assertions are empty, we do nothing. We will answer sat.
  std::shared_ptr<ProofNode> pfn;
  if (!pfns.empty())
  {
    if (pfns.size() == 1)
    {
      pfn = pfns[0];
    }
    else
    {
      pfn = d_pnm->mkNode(ProofRule::AND_INTRO, pfns, {});
    }
    ProofScopeMode m = ProofScopeMode::DEFINITIONS_AND_ASSERTIONS;
    d_ppProof = d_pm->connectProofToAssertions(pfn, d_as, m);
    d_eop.print(d_eout, d_ppProof, m);
  }
  printPendingLemmas();
  Trace("pf-log") << "; log: cnf preprocess input proof end" << std::endl;
}

void ProofLoggerCpc::printPendingLemmas()
{
  d_ppLogged = true;
  for (size_t i = d_numLemmasPrinted, nlemmas = d_lemmaPfs.size(); i < nlemmas;
       i++)
  {
    d_eop.printNext(d_eout, d_lemmaPfs[i]);
  }
  d_numLemmasPrinted = d_lemmaPfs.size();
}

void ProofLoggerCpc::logLemmaProof(std::shared_ptr<ProofNode>& pfn)
{
  d_lemmaPfs.emplace_back(pfn);
  // Theory lemmas may be logged before the preprocessing proof, e.g. when
  // they are generated while asserting the input formulas. We defer printing
  // them until the preprocessing proof has been printed, since the latter
  // must be printed first.
  if (d_ppLogged)
  {
    printPendingLemmas();
  }
}

void ProofLoggerCpc::logTheoryLemmaProof(std::shared_ptr<ProofNode>& pfn)
{
  Trace("pf-log") << "; log theory lemma proof start " << pfn->getResult()
                  << std::endl;
  logLemmaProof(pfn);
  Trace("pf-log") << "; log theory lemma proof end" << std::endl;
}

void ProofLoggerCpc::logTheoryLemma(const Node& n)
{
  Trace("pf-log") << "; log theory lemma start " << n << std::endl;
  std::shared_ptr<ProofNode> ptl =
      d_pnm->mkTrustedNode(TrustId::THEORY_LEMMA, {}, {}, n);
  logLemmaProof(ptl);
  Trace("pf-log") << "; log theory lemma end" << std::endl;
}

void ProofLoggerCpc::logSatRefutation()
{
  Trace("pf-log") << "; log SAT refutation start" << std::endl;
  std::vector<std::shared_ptr<ProofNode>> premises;
  Assert(d_ppProof->getRule() == ProofRule::SCOPE);
  Assert(d_ppProof->getChildren()[0]->getRule() == ProofRule::SCOPE);
  std::shared_ptr<ProofNode> ppBody =
      d_ppProof->getChildren()[0]->getChildren()[0];
  premises.emplace_back(ppBody);
  premises.insert(premises.end(), d_lemmaPfs.begin(), d_lemmaPfs.end());
  Node f = nodeManager()->mkConst(false);
  std::shared_ptr<ProofNode> psr =
      d_pnm->mkNode(ProofRule::SAT_REFUTATION, premises, {}, f);
  d_eop.printNext(d_eout, psr);
  Trace("pf-log") << "; log SAT refutation end" << std::endl;
  // for now, to avoid checking failure
  d_eout.getOStream() << "(exit)" << std::endl;
}

void ProofLoggerCpc::logSatRefutationProof(std::shared_ptr<ProofNode>& pfn)
{
  Trace("pf-log") << "; log SAT refutation proof start" << std::endl;
  // connect to preprocessed
  std::shared_ptr<ProofNode> spf =
      d_pm->connectProofToAssertions(pfn, d_as, ProofScopeMode::NONE);
  d_eop.printNext(d_eout, spf);
  Trace("pf-log") << "; log SAT refutation proof end" << std::endl;
  // for now, to avoid checking failure
  d_eout.getOStream() << "(exit)" << std::endl;
}

}  // namespace cvc5::internal
