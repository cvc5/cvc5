/*********************                                                        */
/*! \file lemma_proof.h
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

#include "cvc4_private.h"

#ifndef __CVC4__LEMMA_PROOF_H
#define __CVC4__LEMMA_PROOF_H

#include "expr/expr.h"
#include "proof/clause_id.h"
#include "prop/sat_solver_types.h"
#include "util/proof.h"
#include "expr/node.h"

namespace CVC4 {

class LemmaProofRecipe {
public:
  class ProofStep {
  public:
    ProofStep(theory::TheoryId theory, Node literalToProve);
    theory::TheoryId getTheory() const;
    Node getLiteral() const;
    void addAssertion(const Node& assertion);
    std::set<Node> getAssertions() const;

  private:
    theory::TheoryId d_theory;
    Node d_literalToProve;
    std::set<Node> d_assertions;
  };

  //* The lemma assertions and owner */
  void addBaseAssertion(Node baseAssertion);
  std::set<Node> getBaseAssertions() const;
  theory::TheoryId getTheory() const;

  //* Rewrite rules */
  typedef std::map<Node, Node>::const_iterator RewriteIterator;
  RewriteIterator rewriteBegin() const;
  RewriteIterator rewriteEnd() const;

  void addRewriteRule(Node assertion, Node explanation);
  bool wasRewritten(Node assertion) const;
  Node getExplanation(Node assertion) const;

  //* Original lemma */
  void setOriginalLemma(Node lemma);
  Node getOriginalLemma() const;

  //* Proof Steps */
  void addStep(ProofStep& proofStep);
  const ProofStep* getStep(unsigned index) const;
  ProofStep* getStep(unsigned index);
  unsigned getNumSteps() const;
  std::set<Node> getMissingAssertionsForStep(unsigned index) const;
  bool simpleLemma() const;
  bool compositeLemma() const;

  void dump(const char *tag) const;
  bool operator<(const LemmaProofRecipe& other) const;

private:
  //* The list of assertions for this lemma */
  std::set<Node> d_baseAssertions;

  //* The various steps needed to derive the empty clause */
  std::list<ProofStep> d_proofSteps;

  //* A map from assertions to their rewritten explanations (toAssert --> toExplain) */
  std::map<Node, Node> d_assertionToExplanation;

  //* The original lemma, as asserted by the owner theory solver */
  Node d_originalLemma;
};

} /* CVC4 namespace */

#endif /* __CVC4__LEMMA_PROOF_H */
