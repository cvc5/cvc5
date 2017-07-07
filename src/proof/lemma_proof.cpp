/*********************                                                        */
/*! \file lemma_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Guy Katz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** A class for recoding the steps required in order to prove a theory lemma.

**/

#include "proof/lemma_proof.h"
#include "theory/rewriter.h"

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

void LemmaProofRecipe::ProofStep::addAssertion(const Node& assertion) {
  d_assertions.insert(assertion);
}

std::set<Node> LemmaProofRecipe::ProofStep::getAssertions() const {
  return d_assertions;
}

void LemmaProofRecipe::addStep(ProofStep& proofStep) {
  d_proofSteps.push_front(proofStep);
}

std::set<Node> LemmaProofRecipe::getMissingAssertionsForStep(unsigned index) const {
  Assert(index < d_proofSteps.size());

  std::set<Node> existingAssertions = getBaseAssertions();

  std::list<ProofStep>::const_iterator step = d_proofSteps.begin();
  while (index != 0) {
    existingAssertions.insert(step->getLiteral().negate());
    ++step;
    --index;
  }

  std::set<Node> neededAssertions = step->getAssertions();

  std::set<Node> result;
  std::set_difference(neededAssertions.begin(), neededAssertions.end(),
                      existingAssertions.begin(), existingAssertions.end(),
                      std::inserter(result, result.begin()));
  return result;
}

void LemmaProofRecipe::dump(const char *tag) const {

  if (d_proofSteps.size() == 1) {
    Debug(tag) << std::endl << "[Simple lemma]" << std::endl << std::endl;
  }

  if (d_originalLemma != Node()) {
    Debug(tag) << std::endl << "Original lemma: " << d_originalLemma << std::endl << std::endl;
  }

  unsigned count = 1;
  Debug(tag) << "Base assertions:" << std::endl;
  for (std::set<Node>::iterator baseIt = d_baseAssertions.begin();
       baseIt != d_baseAssertions.end();
       ++baseIt) {
    Debug(tag) << "\t#" << count << ": " << "\t" << *baseIt << std::endl;
    ++count;
  }

  Debug(tag) << std::endl << std::endl << "Proof steps:" << std::endl;

  count = 1;
  for (std::list<ProofStep>::const_iterator step = d_proofSteps.begin(); step != d_proofSteps.end(); ++step) {
    Debug(tag) << "\tStep #" << count << ": " << "\t[" << step->getTheory() << "] ";
    if (step->getLiteral() == Node()) {
      Debug(tag) << "Contradiction";
    } else {
      Debug(tag) << step->getLiteral();
    }

    Debug(tag) << std::endl;

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

void LemmaProofRecipe::addBaseAssertion(Node baseAssertion) {
  d_baseAssertions.insert(baseAssertion);
}

std::set<Node> LemmaProofRecipe::getBaseAssertions() const {
  return d_baseAssertions;
}

theory::TheoryId LemmaProofRecipe::getTheory() const {
  Assert(d_proofSteps.size() > 0);
  return d_proofSteps.back().getTheory();
}

void LemmaProofRecipe::addRewriteRule(Node assertion, Node explanation) {
  if (d_assertionToExplanation.find(assertion) != d_assertionToExplanation.end()) {
    Assert(d_assertionToExplanation[assertion] == explanation);
  }

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
    return d_baseAssertions < other.d_baseAssertions;
  }

bool LemmaProofRecipe::simpleLemma() const {
  return d_proofSteps.size() == 1;
}

bool LemmaProofRecipe::compositeLemma() const {
  return !simpleLemma();
}

const LemmaProofRecipe::ProofStep* LemmaProofRecipe::getStep(unsigned index) const {
  Assert(index < d_proofSteps.size());

  std::list<ProofStep>::const_iterator it = d_proofSteps.begin();
  while (index != 0) {
    ++it;
    --index;
  }

  return &(*it);
}

LemmaProofRecipe::ProofStep* LemmaProofRecipe::getStep(unsigned index) {
  Assert(index < d_proofSteps.size());

  std::list<ProofStep>::iterator it = d_proofSteps.begin();
  while (index != 0) {
    ++it;
    --index;
  }

  return &(*it);
}

unsigned LemmaProofRecipe::getNumSteps() const {
  return d_proofSteps.size();
}

void LemmaProofRecipe::setOriginalLemma(Node lemma) {
  d_originalLemma = lemma;
}

Node LemmaProofRecipe::getOriginalLemma() const {
  return d_originalLemma;
}


} /* namespace CVC4 */
