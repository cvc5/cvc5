/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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
#include "proof/alethe/alethe_node_converter.h"
#include "proof/alethe/alethe_post_processor.h"
#include "proof/alethe/alethe_printer.h"
#include "proof/dot/dot_printer.h"
#include "proof/lfsc/lfsc_post_processor.h"
#include "proof/lfsc/lfsc_printer.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "smt/assertions.h"
#include "smt/difficulty_post_processor.h"
#include "smt/env.h"
#include "smt/preprocess_proof_generator.h"
#include "smt/proof_post_processor.h"

namespace cvc5::internal {
namespace smt {

PfManager::PfManager(Env& env)
    : EnvObj(env),
      d_pchecker(new ProofChecker(
          statisticsRegistry(),
          options().proof.proofCheck,
          static_cast<uint32_t>(options().proof.proofPedantic))),
      d_pnm(new ProofNodeManager(
          env.getOptions(), env.getRewriter(), d_pchecker.get())),
      d_pppg(nullptr),
      d_pfpp(nullptr)
{
  // now construct preprocess proof generator
  d_pppg = std::make_unique<PreprocessProofGenerator>(
      env, env.getUserContext(), "smt::PreprocessProofGenerator");
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
  // the Alethe reconstruction, so we disable the update of scoped
  // assumptions (which would disable the update of B1 in this case).
  d_pfpp = std::make_unique<ProofPostproccess>(
      env,
      d_pppg.get(),
      nullptr,
      options().proof.proofFormatMode != options::ProofFormatMode::ALETHE);

  // add rules to eliminate here
  if (options().proof.proofGranularityMode
      != options::ProofGranularityMode::MACRO)
  {
    d_pfpp->setEliminateRule(PfRule::MACRO_SR_EQ_INTRO);
    d_pfpp->setEliminateRule(PfRule::MACRO_SR_PRED_INTRO);
    d_pfpp->setEliminateRule(PfRule::MACRO_SR_PRED_ELIM);
    d_pfpp->setEliminateRule(PfRule::MACRO_SR_PRED_TRANSFORM);
    d_pfpp->setEliminateRule(PfRule::MACRO_RESOLUTION_TRUST);
    d_pfpp->setEliminateRule(PfRule::MACRO_RESOLUTION);
    d_pfpp->setEliminateRule(PfRule::MACRO_ARITH_SCALE_SUM_UB);
    if (options().proof.proofGranularityMode
        != options::ProofGranularityMode::REWRITE)
    {
      d_pfpp->setEliminateRule(PfRule::SUBS);
      d_pfpp->setEliminateRule(PfRule::REWRITE);
      if (options().proof.proofGranularityMode
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

std::shared_ptr<ProofNode> PfManager::connectProofToAssertions(
    std::shared_ptr<ProofNode> pfn, Assertions& as)
{
  // Note this assumes that connectProofToAssertions is only called once per
  // unsat response. This method would need to cache its result otherwise.
  Trace("smt-proof")
      << "SolverEngine::connectProofToAssertions(): get proof body...\n";

  if (TraceIsOn("smt-proof-debug"))
  {
    Trace("smt-proof-debug")
        << "SolverEngine::connectProofToAssertions(): Proof node for false:\n";
    Trace("smt-proof-debug") << *pfn.get() << std::endl;
    Trace("smt-proof-debug") << "=====" << std::endl;
  }

  std::vector<Node> assertions;
  getAssertions(as, assertions);

  if (TraceIsOn("smt-proof"))
  {
    Trace("smt-proof")
        << "SolverEngine::connectProofToAssertions(): get free assumptions..."
        << std::endl;
    std::vector<Node> fassumps;
    expr::getFreeAssumptions(pfn.get(), fassumps);
    Trace("smt-proof") << "SolverEngine::connectProofToAssertions(): initial "
                          "free assumptions are:\n";
    for (const Node& a : fassumps)
    {
      Trace("smt-proof") << "- " << a << std::endl;
    }

    Trace("smt-proof")
        << "SolverEngine::connectProofToAssertions(): assertions are:\n";
    for (const Node& n : assertions)
    {
      Trace("smt-proof") << "- " << n << std::endl;
    }
    Trace("smt-proof") << "=====" << std::endl;
  }

  Trace("smt-proof")
      << "SolverEngine::connectProofToAssertions(): postprocess...\n";
  Assert(d_pfpp != nullptr);
  d_pfpp->process(pfn);

  Trace("smt-proof")
      << "SolverEngine::connectProofToAssertions(): make scope...\n";

  // Now make the final scope, which ensures that the only open leaves of the
  // proof are the assertions. If we are pruning the input, we will try to
  // minimize the used assertions.
  return d_pnm->mkScope(pfn, assertions, true, options().proof.proofPruneInput);
}

void PfManager::printProof(std::ostream& out, std::shared_ptr<ProofNode> fp)
{
  Trace("smt-proof") << "PfManager::printProof: start" << std::endl;
  // if we are in incremental mode, we don't want to invalidate the proof
  // nodes in fp, since these may be reused in further check-sat calls
  if (options().base.incrementalSolving
      && options().proof.proofFormatMode != options::ProofFormatMode::NONE)
  {
    fp = d_pnm->clone(fp);
  }

  // according to the proof format, post process and print the proof node
  if (options().proof.proofFormatMode == options::ProofFormatMode::DOT)
  {
    proof::DotPrinter dotPrinter(d_env);
    dotPrinter.print(out, fp.get());
  }
  else if (options().proof.proofFormatMode == options::ProofFormatMode::ALETHE)
  {
    proof::AletheNodeConverter anc;
    proof::AletheProofPostprocess vpfpp(
        d_env, anc, options().proof.proofAletheResPivots);
    vpfpp.process(fp);
    proof::AletheProofPrinter vpp;
    vpp.print(out, fp);
  }
  else if (options().proof.proofFormatMode == options::ProofFormatMode::LFSC)
  {
    Assert(fp->getRule() == PfRule::SCOPE);
    std::vector<Node> assertions = fp->getArguments();
    proof::LfscNodeConverter ltp;
    proof::LfscProofPostprocess lpp(d_env, ltp);
    lpp.process(fp);
    proof::LfscPrinter lp(ltp);
    lp.print(out, assertions, fp.get());
  }
  else if (options().proof.proofFormatMode == options::ProofFormatMode::TPTP)
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
    // we call the printing method explicitly because we may want to print the
    // final proof node with conclusions
    fp->printDebug(out, options().proof.proofPrintConclusion);
    out << "\n)\n";
  }
}

void PfManager::translateDifficultyMap(std::map<Node, Node>& dmap,
                                       Assertions& as)
{
  Trace("difficulty-proc") << "Translate difficulty start" << std::endl;
  Trace("difficulty") << "PfManager::translateDifficultyMap" << std::endl;
  if (dmap.empty())
  {
    return;
  }
  std::map<Node, Node> dmapp = dmap;
  dmap.clear();
  Trace("difficulty-proc") << "Get ppAsserts" << std::endl;
  std::vector<Node> ppAsserts;
  for (const std::pair<const Node, Node>& ppa : dmapp)
  {
    Trace("difficulty") << "  preprocess difficulty: " << ppa.second << " for "
                        << ppa.first << std::endl;
    // The difficulty manager should only report difficulty for preprocessed
    // assertions, or we will get an open proof below. This is ensured
    // internally by the difficuly manager.
    ppAsserts.push_back(ppa.first);
  }
  Trace("difficulty-proc") << "Make SAT refutation" << std::endl;
  // assume a SAT refutation from all input assertions that were marked
  // as having a difficulty
  CDProof cdp(d_env);
  Node fnode = NodeManager::currentNM()->mkConst(false);
  cdp.addStep(fnode, PfRule::SAT_REFUTATION, ppAsserts, {});
  std::shared_ptr<ProofNode> pf = cdp.getProofFor(fnode);
  Trace("difficulty-proc") << "Get final proof" << std::endl;
  std::shared_ptr<ProofNode> fpf = connectProofToAssertions(pf, as);
  Trace("difficulty-debug") << "Final proof is " << *fpf.get() << std::endl;
  Assert(fpf->getRule() == PfRule::SCOPE);
  fpf = fpf->getChildren()[0];
  // analyze proof
  Assert(fpf->getRule() == PfRule::SAT_REFUTATION);
  const std::vector<std::shared_ptr<ProofNode>>& children = fpf->getChildren();
  DifficultyPostprocessCallback dpc;
  ProofNodeUpdater dpnu(d_env, dpc);
  Trace("difficulty-proc") << "Compute accumulated difficulty" << std::endl;
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
  Trace("difficulty-proc") << "Translate difficulty end" << std::endl;
}

ProofChecker* PfManager::getProofChecker() const { return d_pchecker.get(); }

ProofNodeManager* PfManager::getProofNodeManager() const { return d_pnm.get(); }

rewriter::RewriteDb* PfManager::getRewriteDatabase() const { return nullptr; }

smt::PreprocessProofGenerator* PfManager::getPreprocessProofGenerator() const
{
  return d_pppg.get();
}

void PfManager::getAssertions(Assertions& as,
                              std::vector<Node>& assertions)
{
  // note that the assertion list is always available
  const context::CDList<Node>& al = as.getAssertionList();
  for (const Node& a : al)
  {
    assertions.push_back(a);
  }
}

}  // namespace smt
}  // namespace cvc5::internal
