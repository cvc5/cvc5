/*********************                                                        */
/*! \file lemma_proof.h
** \verbatim
**
** \brief A class for recoding the steps required in order to prove a theory lemma.
**
** A class for recoding the steps required in order to prove a theory lemma.
**
**/

#include "proof/lemma_proof.h"

namespace CVC4 {

LemmaProofRecipe::ProofStep::ProofStep(theory::TheoryId theory, Node literalToProve) :
  d_theory(theory), d_literalToProve(literalToProve) {
}

theory::TheoryId LemmaProofRecipe::ProofStep::getTheory() const {
  return d_theory;
}

Node LemmaProofRecipe::ProofStep::getLiteral() const {
  return d_literalToProve;
}

void LemmaProofRecipe::ProofStep::addAssumption(const Node& assumption) {
  d_assumptions.insert(assumption);
}

std::set<Node> LemmaProofRecipe::ProofStep::getAssumptions() const {
  return d_assumptions;
}

void LemmaProofRecipe::addStep(ProofStep& proofStep) {
  std::list<ProofStep>::iterator existingFirstStep = d_proofSteps.begin();
  d_proofSteps.push_front(proofStep);
}

std::set<Node> LemmaProofRecipe::getMissingAssertionsForStep(unsigned index) const {
  Assert(index < d_proofSteps.size());

  std::set<Node> existingAssertions = d_assertions;

  std::list<ProofStep>::const_iterator step = d_proofSteps.begin();
  while (index != 0) {
    existingAssertions.insert(step->getLiteral().negate());
    ++step;
    --index;
  }

  std::set<Node> neededAssertions = step->getAssumptions();

  std::set<Node> result;
  std::set_difference(neededAssertions.begin(), neededAssertions.end(),
                      existingAssertions.begin(), existingAssertions.end(),
                      std::inserter(result, result.begin()));
  return result;
}

void LemmaProofRecipe::dump(const char *tag) const {
  if (d_proofSteps.empty()) {
    Debug(tag) << std::endl << "[Simple lemma]" << std::endl;
    Assert(d_assertionToExplanation.empty());
  } else {
    Debug(tag) << std::endl << "Proof steps:" << std::endl;

    unsigned count = 1;
    for (std::list<ProofStep>::const_iterator step = d_proofSteps.begin(); step != d_proofSteps.end(); ++step) {
      Debug(tag) << "\tStep #" << count << ": " << "\t[" << step->getTheory() << "] " << step->getLiteral()
                 << std::endl;

      std::set<Node> missingAssertions = getMissingAssertionsForStep(count - 1);
      for (std::set<Node>::const_iterator it = missingAssertions.begin(); it != missingAssertions.end(); ++it) {
        Debug(tag) << "\t\t\tMissing assertion for step: " << *it << std::endl;
      }

      Debug(tag) << std::endl;
      ++count;
    }

    if (!d_assertionToExplanation.empty()) {
      Debug(tag) << std::endl << "Rewrites used:" << std::endl;
      count = 1;
      for (std::map<Node, Node>::const_iterator rewrite = d_assertionToExplanation.begin();
           rewrite != d_assertionToExplanation.end();
           ++rewrite) {
        Debug(tag) << "\tRewrite #" << count << ":" << std::endl
                   << "\t\t" << rewrite->first
                   << std::endl << "\t\trewritten into" << std::endl
                   << "\t\t" << rewrite->second
                   << std::endl << std::endl;
        ++count;
      }
    }
  }
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

void LemmaProofRecipe::addRewriteRule(Node assertion, Node explanation) {
  Debug("gk::temp") << "LemmaProofRecipe::addRewriteRule: " << assertion << " --> " << explanation << std::endl;
  // if (d_explanationToAssertion.find(explanation) != d_explanationToAssertion.end()) {
  //   Debug("gk::temp") << "LemmaProofRecipe::addRewriteRule: existing rewrite: " << d_explanationToAssertion[explanation] << std::endl;
  //   Assert(d_explanationToAssertion[explanation] == assertion);
  // }

  if (d_assertionToExplanation.find(assertion) != d_assertionToExplanation.end()) {
    Assert(d_assertionToExplanation[assertion] == explanation);
  }

  // d_explanationToAssertion[explanation] = assertion;
  d_assertionToExplanation[assertion] = explanation;
}

bool LemmaProofRecipe::wasRewritten(Node assertion) const {
  return d_assertionToExplanation.find(assertion) != d_assertionToExplanation.end();
}

Node LemmaProofRecipe::getExplanation(Node assertion) const {
  Assert(d_assertionToExplanation.find(assertion) != d_assertionToExplanation.end());
  return d_assertionToExplanation.find(assertion)->second;
}

LemmaProofRecipe::RewriteIterator LemmaProofRecipe::rewriteBegin() const {
  return d_assertionToExplanation.begin();
}

LemmaProofRecipe::RewriteIterator LemmaProofRecipe::rewriteEnd() const {
  return d_assertionToExplanation.end();
}

bool LemmaProofRecipe::operator<(const LemmaProofRecipe& other) const {
    return d_assertions < other.d_assertions;
  }

bool LemmaProofRecipe::simpleLemma() const {
  return d_proofSteps.empty();
}

bool LemmaProofRecipe::compositeLemma() const {
  return !simpleLemma();
}

LemmaProofRecipe::ProofStep LemmaProofRecipe::getStep(unsigned index) const {
  Assert(index < d_proofSteps.size());

  std::list<ProofStep>::const_iterator it = d_proofSteps.begin();
  while (index != 0) {
    ++it;
    --index;
  }

  return *it;
}

unsigned LemmaProofRecipe::getNumSteps() const {
  return d_proofSteps.size();
}

} /* namespace CVC4 */
