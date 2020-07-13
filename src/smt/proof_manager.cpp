/*********************                                                        */
/*! \file proof_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The proof manager of the SMT engine
 **/

#include "smt/proof_manager.h"

#include "options/smt_options.h"
#include "options/base_options.h"

namespace CVC4 {
namespace smt {

PfManager::PfManager(SmtEngine * smte, context::CDList<Node>* al) :
    d_assertionList(al),
    d_pchecker(new ProofChecker),
    d_pnm(new ProofNodeManager(d_pchecker.get())),
    d_rewriteDb(new theory::RewriteDb),
    d_pppg(new PreprocessProofGenerator(d_pnm.get())),
    d_pfpp(new ProofPostproccess(d_pnm.get(), smte)),
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

PfManager::~PfManager()
{
  
}
  
void PfManager::setFinalProof(ProofGenerator * pg)
{
  Trace("smt-proof") << "SmtEngine::setFinalProof(): get proof body...\n";

  // d_finalProof should just be a ProofNode
  std::shared_ptr<ProofNode> body =
      pg
          ->getProofFor(d_false)
          ->clone();

  if (Trace.isOn("smt-proof"))
  {
    Trace("smt-proof") << "SmtEngine::setFinalProof(): Proof node for false:\n";
    std::stringstream ss;
    body->printDebug(ss);
    Trace("smt-proof") << ss.str() << std::endl;
    Trace("smt-proof") << "=====" << std::endl;
  }

  std::vector<Node> assertions;
  Trace("smt-proof") << "SmtEngine::setFinalProof(): assertions are:\n";
  for (context::CDList<Node>::const_iterator i = d_assertionList->begin();
       i != d_assertionList->end();
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

void PfManager::printProof(ProofGenerator * pg)
{
  std::shared_ptr<ProofNode> fp = getFinalProof(pg);
  *options::out() << "(proof\n";
  fp->printDebug(*options::out());
  *options::out() << "\n)\n";
}

ProofChecker* PfManager::getProofChecker() const { return d_pchecker.get(); }

ProofNodeManager* PfManager::getProofNodeManager() const { return d_pnm.get(); }

theory::RewriteDb * PfManager::getRewriteDatabase() const { return d_rewriteDb.get(); }

std::shared_ptr<ProofNode> PfManager::getFinalProof(ProofGenerator * pg) 
{ 
  // TODO: don't recompute if already done so?
  setFinalProof(pg);
  Assert(d_finalProof);
  return d_finalProof; 
}
 
}/* smt namespace */
}/* CVC4 namespace */
