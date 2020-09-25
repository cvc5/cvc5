/*********************                                                        */
/*! \file proof_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The proof manager of the SMT engine
 **/

#include "smt/proof_manager.h"

#include "expr/proof_node_algorithm.h"
#include "options/base_options.h"
#include "options/smt_options.h"
#include "smt/assertions.h"

namespace CVC4 {
namespace smt {

PfManager::PfManager(SmtEngine* smte)
    : d_pchecker(new ProofChecker(options::proofNewPedantic())),
      d_pnm(new ProofNodeManager(d_pchecker.get())),
      d_pppg(new PreprocessProofGenerator(d_pnm.get())),
      d_pfpp(new ProofPostproccess(d_pnm.get(), smte, d_pppg.get())),
      d_finalProof(nullptr)
{
  // add rules to eliminate here
  if (options::proofGranularityMode() != options::ProofGranularityMode::OFF)
  {
    d_pfpp->setEliminateRule(PfRule::MACRO_SR_EQ_INTRO);
    d_pfpp->setEliminateRule(PfRule::MACRO_SR_PRED_INTRO);
    d_pfpp->setEliminateRule(PfRule::MACRO_SR_PRED_ELIM);
    d_pfpp->setEliminateRule(PfRule::MACRO_SR_PRED_TRANSFORM);
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
  }
  d_false = NodeManager::currentNM()->mkConst(false);
}

PfManager::~PfManager() {}

void PfManager::setFinalProof(ProofGenerator* pg, context::CDList<Node>* al)
{
  Assert(al != nullptr);
  // Note this assumes that setFinalProof is only called once per unsat
  // response. This method would need to cache its result otherwise.
  Trace("smt-proof") << "SmtEngine::setFinalProof(): get proof body...\n";

  // d_finalProof should just be a ProofNode
  std::shared_ptr<ProofNode> body = pg->getProofFor(d_false)->clone();

  if (Trace.isOn("smt-proof-debug"))
  {
    Trace("smt-proof-debug")
        << "SmtEngine::setFinalProof(): Proof node for false:\n";
    Trace("smt-proof-debug") << *body.get() << std::endl;
    Trace("smt-proof-debug") << "=====" << std::endl;
  }

  if (Trace.isOn("smt-proof"))
  {
    std::vector<Node> fassumps;
    expr::getFreeAssumptions(body.get(), fassumps);
    Trace("smt-proof")
        << "SmtEngine::setFinalProof(): initial free assumptions are:\n";
    for (const Node& a : fassumps)
    {
      Trace("smt-proof") << "- " << a << std::endl;
    }
  }

  std::vector<Node> assertions;
  Trace("smt-proof") << "SmtEngine::setFinalProof(): assertions are:\n";
  for (context::CDList<Node>::const_iterator i = al->begin(); i != al->end();
       ++i)
  {
    Node n = *i;
    Trace("smt-proof") << "- " << n << std::endl;
    assertions.push_back(n);
  }
  Trace("smt-proof") << "=====" << std::endl;

  Trace("smt-proof") << "SmtEngine::setFinalProof(): postprocess...\n";
  Assert(d_pfpp != nullptr);
  d_pfpp->process(body);

  Trace("smt-proof") << "SmtEngine::setFinalProof(): make scope...\n";

  // Now make the final scope, which ensures that the only open leaves
  // of the proof are the assertions.
  d_finalProof = d_pnm->mkScope(body, assertions);
  Trace("smt-proof") << "SmtEngine::setFinalProof(): finished.\n";
}

void PfManager::printProof(ProofGenerator* pg, Assertions& as)
{
  Trace("smt-proof") << "PfManager::printProof: start" << std::endl;
  std::shared_ptr<ProofNode> fp = getFinalProof(pg, as);
  // TODO (proj #37) according to the proof format, post process the proof node
  // TODO (proj #37) according to the proof format, print the proof node
  // leanPrinter(out, fp.get());
  std::ostream& out = *options::out();
  out << "(proof\n";
  out << *fp;
  out << "\n)\n";
}

void PfManager::checkProof(ProofGenerator* pg, Assertions& as)
{
  Trace("smt-proof") << "PfManager::checkProof: start" << std::endl;
  std::shared_ptr<ProofNode> fp = getFinalProof(pg, as);
  Trace("smt-proof") << "PfManager::checkProof: returned " << *fp.get()
                     << std::endl;
}

ProofChecker* PfManager::getProofChecker() const { return d_pchecker.get(); }

ProofNodeManager* PfManager::getProofNodeManager() const { return d_pnm.get(); }

smt::PreprocessProofGenerator* PfManager::getPreprocessProofGenerator() const
{
  return d_pppg.get();
}

std::shared_ptr<ProofNode> PfManager::getFinalProof(ProofGenerator* pg,
                                                    Assertions& as)
{
  context::CDList<Node>* al = as.getAssertionList();
  setFinalProof(pg, al);
  Assert(d_finalProof);
  return d_finalProof;
}

}  // namespace smt
}  // namespace CVC4
