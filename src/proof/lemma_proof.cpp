/*********************                                                        */
/*! \file lemma_proof.cpp
 ** \verbatim
 **
 ** \brief A manager for proving theory lemmas.
 **
 ** A manager for proving theory lemmas.
 **/

#include "proof/lemma_proof.h"

namespace CVC4 {

void LemmaProofRecipe::addStep(ProofStep& proofStep) {
  std::list<ProofStep>::iterator existingFirstStep = d_proofSteps.begin();
  d_proofSteps.push_front(proofStep);

  // if (existingFirstStep != d_proofSteps.end()) {
  //   // Make sure that the previous first step's assertions are precisely the new
  //   // first step's assertions + literalToProve
  //   Assert(proofStep.d_assertions.size() + 1 == existingFirstStep->d_assertions.size());
  //   std::set<Node> newLiterals;
  //   std::set_difference(proofStep.d_assertions.begin(),
  //                       proofStep.d_assertions.end(),
  //                       existingFirstStep->d_assertions.begin(),
  //                       existingFirstStep->d_assertions.end(),
  //                       std::inserter(newLiterals, newLiterals.end()));

  //   Assert(newLiterals.size() == 1);
  //   Assert((*newLiterals.begin()) == proofStep.d_literalToProve);
  // } else {
  //   // We've just added the final step, so it must lead to a negation.
  //   Assert(proofStep.d_literalToProve == NodeManager::currentNM()->mkConst<bool>(false));
  // }
}

void LemmaProofRecipe::dump(const char *tag) const {
  Debug(tag) << std::endl << "**********" << std::endl;
  Debug(tag) << "Printing proof recipe for lemma: " << std::endl;
  Debug(tag) << "Owner theory: " << d_theory << std::endl;

  unsigned assertionCount = 1;
  for (std::set<Node>::iterator assertion = d_assertions.begin(); assertion != d_assertions.end(); ++assertion) {
    Debug(tag) << "\tAssertion #" << assertionCount << ": " << *assertion << std::endl;
    ++assertionCount;
  }

  Debug(tag) << std::endl << "Proof steps:" << std::endl;

  unsigned stepCount = 1;
  for (std::list<ProofStep>::const_iterator step = d_proofSteps.begin(); step != d_proofSteps.end(); ++step) {
    Debug(tag) << "[" << step->d_theory << "]" << "\tStep #" << stepCount << ": " << step->d_literalToProve << std::endl << std::endl;
    ++stepCount;
  }

  Debug(tag) << std::endl << "**********" << std::endl << std::endl;
}

void LemmaProofRecipe::addAssertion(Node assertion) {
  d_assertions.insert(assertion);
}

std::set<Node> LemmaProofRecipe::getAssertions() const {
  return d_assertions;
}

void LemmaProofRecipe::setTheory(theory::TheoryId theory) {
  d_theory = theory;
}

theory::TheoryId LemmaProofRecipe::getTheory() const {
  return d_theory;
}

} /* namespace CVC4 */
