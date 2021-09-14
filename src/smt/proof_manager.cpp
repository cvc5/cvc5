/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Diego Della Rocca de Camargos
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The proof manager of the SMT engine.
 */

#include "smt/proof_manager.h"

#include "options/base_options.h"
#include "options/main_options.h"
#include "options/proof_options.h"
#include "options/smt_options.h"
#include "proof/dot/dot_printer.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "smt/assertions.h"
#include "smt/difficulty_post_processor.h"
#include "smt/env.h"
#include "smt/preprocess_proof_generator.h"
#include "smt/proof_post_processor.h"

namespace cvc5 {
namespace smt {

PfManager::PfManager(Env& env)
    : EnvObj(env),
      d_pchecker(new ProofChecker(
          options().proof.proofCheck == options::ProofCheckMode::EAGER,
          options().proof.proofPedantic)),
      d_pnm(new ProofNodeManager(d_pchecker.get())),
      d_pppg(new PreprocessProofGenerator(
          d_pnm.get(), env.getUserContext(), "smt::PreprocessProofGenerator")),
      d_pfpp(nullptr),
      d_finalProof(nullptr)
{
  // enable proof support in the environment/rewriter
  d_env.setProofNodeManager(d_pnm.get());
  // Now, initialize the proof postprocessor with the environment.
  // By default the post-processor will update all assumptions, which
  // can lead to SCOPE subproofs of the form
  //   A
  //  ...
  //   B1    B2
  //  ...   ...
  // ------------
  //      C
  // ------------- SCOPE [B1, B2]
  // B1 ^ B2 => C
  //
  // where A is an available assumption from outside the scope (note
  // that B1 was an assumption of this SCOPE subproof but since it could
  // be inferred from A, it was updated). This shape is problematic for
  // the veriT reconstruction, so we disable the update of scoped
  // assumptions (which would disable the update of B1 in this case).
  d_pfpp.reset(new ProofPostproccess(
      env,
      d_pppg.get(),
      nullptr,
      options::proofFormatMode() != options::ProofFormatMode::VERIT));

  // add rules to eliminate here
  if (options::proofGranularityMode() != options::ProofGranularityMode::OFF)
  {
    d_pfpp->setEliminateRule(PfRule::MACRO_SR_EQ_INTRO);
    d_pfpp->setEliminateRule(PfRule::MACRO_SR_PRED_INTRO);
    d_pfpp->setEliminateRule(PfRule::MACRO_SR_PRED_ELIM);
    d_pfpp->setEliminateRule(PfRule::MACRO_SR_PRED_TRANSFORM);
    d_pfpp->setEliminateRule(PfRule::MACRO_RESOLUTION_TRUST);
    d_pfpp->setEliminateRule(PfRule::MACRO_RESOLUTION);
    d_pfpp->setEliminateRule(PfRule::MACRO_ARITH_SCALE_SUM_UB);
    if (options::proofGranularityMode()
        != options::ProofGranularityMode::REWRITE)
    {
      d_pfpp->setEliminateRule(PfRule::SUBS);
      d_pfpp->setEliminateRule(PfRule::REWRITE);
      if (options::proofGranularityMode()
          != options::ProofGranularityMode::THEORY_REWRITE)
      {
        // this eliminates theory rewriting steps with finer-grained DSL rules
        d_pfpp->setEliminateRule(PfRule::THEORY_REWRITE);
      }
    }
    // theory-specific lazy proof reconstruction
    d_pfpp->setEliminateRule(PfRule::STRING_INFERENCE);
    d_pfpp->setEliminateRule(PfRule::BV_BITBLAST);
  }
  d_false = NodeManager::currentNM()->mkConst(false);
}

PfManager::~PfManager() {}

void PfManager::setFinalProof(std::shared_ptr<ProofNode> pfn, Assertions& as)
{
  // Note this assumes that setFinalProof is only called once per unsat
  // response. This method would need to cache its result otherwise.
  Trace("smt-proof") << "SmtEngine::setFinalProof(): get proof body...\n";

  if (Trace.isOn("smt-proof-debug"))
  {
    Trace("smt-proof-debug")
        << "SmtEngine::setFinalProof(): Proof node for false:\n";
    Trace("smt-proof-debug") << *pfn.get() << std::endl;
    Trace("smt-proof-debug") << "=====" << std::endl;
  }

  std::vector<Node> assertions;
  getAssertions(as, assertions);

  if (Trace.isOn("smt-proof"))
  {
    Trace("smt-proof") << "SmtEngine::setFinalProof(): get free assumptions..."
                       << std::endl;
    std::vector<Node> fassumps;
    expr::getFreeAssumptions(pfn.get(), fassumps);
    Trace("smt-proof")
        << "SmtEngine::setFinalProof(): initial free assumptions are:\n";
    for (const Node& a : fassumps)
    {
      Trace("smt-proof") << "- " << a << std::endl;
    }

    Trace("smt-proof") << "SmtEngine::setFinalProof(): assertions are:\n";
    for (const Node& n : assertions)
    {
      Trace("smt-proof") << "- " << n << std::endl;
    }
    Trace("smt-proof") << "=====" << std::endl;
  }

  Trace("smt-proof") << "SmtEngine::setFinalProof(): postprocess...\n";
  Assert(d_pfpp != nullptr);
  d_pfpp->process(pfn);

  Trace("smt-proof") << "SmtEngine::setFinalProof(): make scope...\n";

  // Now make the final scope, which ensures that the only open leaves of the
  // proof are the assertions.
  d_finalProof = d_pnm->mkScope(pfn, assertions);
  Trace("smt-proof") << "SmtEngine::setFinalProof(): finished.\n";
}

void PfManager::printProof(std::ostream& out,
                           std::shared_ptr<ProofNode> pfn,
                           Assertions& as)
{
  Trace("smt-proof") << "PfManager::printProof: start" << std::endl;
  std::shared_ptr<ProofNode> fp = getFinalProof(pfn, as);
  // if we are in incremental mode, we don't want to invalidate the proof
  // nodes in fp, since these may be reused in further check-sat calls
  if (options::incrementalSolving()
      && options::proofFormatMode() != options::ProofFormatMode::NONE)
  {
    fp = d_pnm->clone(fp);
  }
  // TODO (proj #37) according to the proof format, post process the proof node
  // TODO (proj #37) according to the proof format, print the proof node

  // according to the proof format, post process and print the proof node
  if (options::proofFormatMode() == options::ProofFormatMode::DOT)
  {
    proof::DotPrinter dotPrinter;
    dotPrinter.print(out, fp.get());
  }
  else if (options::proofFormatMode() == options::ProofFormatMode::TPTP)
  {
    out << "% SZS output start Proof for " << options().driver.filename
        << std::endl;
    // TODO (proj #37) print in TPTP compliant format
    out << *fp << std::endl;
    out << "% SZS output end Proof for " << options().driver.filename
        << std::endl;
  }
  else
  {
    // otherwise, print using default printer
    out << "(proof\n";
    out << *fp;
    out << "\n)\n";
  }
}
void PfManager::checkProof(std::shared_ptr<ProofNode> pfn, Assertions& as)
{
  Trace("smt-proof") << "PfManager::checkProof: start" << std::endl;
  std::shared_ptr<ProofNode> fp = getFinalProof(pfn, as);
  Trace("smt-proof-debug") << "PfManager::checkProof: returned " << *fp.get()
                           << std::endl;
}

void PfManager::translateDifficultyMap(std::map<Node, Node>& dmap,
                                       Assertions& as)
{
  Trace("difficulty") << "PfManager::translateDifficultyMap" << std::endl;
  if (dmap.empty())
  {
    return;
  }
  std::map<Node, Node> dmapp = dmap;
  dmap.clear();
  std::vector<Node> ppAsserts;
  for (const std::pair<const Node, Node>& ppa : dmapp)
  {
    Trace("difficulty") << "  preprocess difficulty: " << ppa.second << " for "
                        << ppa.first << std::endl;
    ppAsserts.push_back(ppa.first);
  }
  // assume a SAT refutation from all input assertions that were marked
  // as having a difficulty
  CDProof cdp(d_pnm.get());
  Node fnode = NodeManager::currentNM()->mkConst(false);
  cdp.addStep(fnode, PfRule::SAT_REFUTATION, ppAsserts, {});
  std::shared_ptr<ProofNode> pf = cdp.getProofFor(fnode);
  std::shared_ptr<ProofNode> fpf = getFinalProof(pf, as);
  Trace("difficulty-debug") << "Final proof is " << *fpf.get() << std::endl;
  Assert(fpf->getRule() == PfRule::SCOPE);
  fpf = fpf->getChildren()[0];
  // analyze proof
  Assert(fpf->getRule() == PfRule::SAT_REFUTATION);
  const std::vector<std::shared_ptr<ProofNode>>& children = fpf->getChildren();
  DifficultyPostprocessCallback dpc;
  ProofNodeUpdater dpnu(d_pnm.get(), dpc);
  // For each child of SAT_REFUTATION, we increment the difficulty on all
  // "source" free assumptions (see DifficultyPostprocessCallback) by the
  // difficulty of the preprocessed assertion.
  for (const std::shared_ptr<ProofNode>& c : children)
  {
    Node res = c->getResult();
    Assert(dmapp.find(res) != dmapp.end());
    Trace("difficulty-debug") << "  process: " << res << std::endl;
    Trace("difficulty-debug") << "  .dvalue: " << dmapp[res] << std::endl;
    Trace("difficulty-debug") << "  ..proof: " << *c.get() << std::endl;
    if (!dpc.setCurrentDifficulty(dmapp[res]))
    {
      continue;
    }
    dpnu.process(c);
  }
  // get the accumulated difficulty map from the callback
  dpc.getDifficultyMap(dmap);
}

ProofChecker* PfManager::getProofChecker() const { return d_pchecker.get(); }

ProofNodeManager* PfManager::getProofNodeManager() const { return d_pnm.get(); }

rewriter::RewriteDb* PfManager::getRewriteDatabase() const { return nullptr; }

smt::PreprocessProofGenerator* PfManager::getPreprocessProofGenerator() const
{
  return d_pppg.get();
}

std::shared_ptr<ProofNode> PfManager::getFinalProof(
    std::shared_ptr<ProofNode> pfn, Assertions& as)
{
  setFinalProof(pfn, as);
  Assert(d_finalProof);
  return d_finalProof;
}

void PfManager::getAssertions(Assertions& as,
                              std::vector<Node>& assertions)
{
  context::CDList<Node>* al = as.getAssertionList();
  Assert(al != nullptr);
  for (context::CDList<Node>::const_iterator i = al->begin(); i != al->end();
       ++i)
  {
    assertions.push_back(*i);
  }
}

}  // namespace smt
}  // namespace cvc5
