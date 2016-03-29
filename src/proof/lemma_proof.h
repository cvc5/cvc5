/*********************                                                        */
/*! \file lemma_proof.h
** \verbatim
**
** \brief A manager for proving theory lemmas.
**
** A manager for proving theory lemmas.
**
**
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
    ProofStep(theory::TheoryId theory, Node literalToProve) : d_theory(theory), d_literalToProve(literalToProve) {
    }

    theory::TheoryId d_theory;
    Node d_literalToProve;
  };

  void addStep(ProofStep& proofStep);
  void dump(const char *tag) const;
  void addAssertion(Node assertion);
  std::set<Node> getAssertions() const;
  void setTheory(theory::TheoryId theory);
  theory::TheoryId getTheory() const;

private:
  std::set<Node> d_assertions;
  std::list<ProofStep> d_proofSteps;
  theory::TheoryId d_theory;
};

} /* CVC4 namespace */

#endif /* __CVC4__LEMMA_PROOF_H */
