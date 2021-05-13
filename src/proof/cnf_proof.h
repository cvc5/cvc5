/******************************************************************************
 * Top contributors (to current version):
 *   Liana Hadarean, Haniel Barbosa, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A manager for CnfProofs.
 */

#include "cvc5_private.h"

#ifndef CVC5__CNF_PROOF_H
#define CVC5__CNF_PROOF_H

#include <unordered_map>
#include <unordered_set>

#include "context/cdhashmap.h"
#include "proof/clause_id.h"
#include "proof/proof_manager.h"

namespace cvc5 {
namespace prop {
  class CnfStream;
  }  // namespace prop

class CnfProof;

typedef std::unordered_map<Node, Node> NodeToNode;
typedef std::unordered_set<ClauseId> ClauseIdSet;

typedef context::CDHashMap<ClauseId, Node> ClauseIdToNode;
typedef std::pair<Node, Node> NodePair;
typedef std::set<NodePair> NodePairSet;

typedef std::unordered_set<Node> NodeSet;

class CnfProof {
protected:
 cvc5::prop::CnfStream* d_cnfStream;

 /** Map from ClauseId to the assertion that lead to adding this clause **/
 ClauseIdToNode d_clauseToAssertion;

 /** Top of stack is assertion currently being converted to CNF. Also saves
  * whether it is input (rather than a lemma). **/
 std::vector<std::pair<Node, bool>> d_currentAssertionStack;

 /** Map from top-level fact to facts/assertion that it follows from **/
 NodeToNode d_cnfDeps;

 ClauseIdSet d_explanations;

 // The clause ID of the unit clause defining the true SAT literal.
 ClauseId d_trueUnitClause;
 // The clause ID of the unit clause defining the false SAT literal.
 ClauseId d_falseUnitClause;

 std::string d_name;
public:
 CnfProof(cvc5::prop::CnfStream* cnfStream,
          context::Context* ctx,
          const std::string& name);
 ~CnfProof();

 /** Methods for logging what the CnfStream does **/
 // map the clause back to the current assertion where it came from
 void registerConvertedClause(ClauseId clause);

 /** Clause is one of the clauses defining top-level assertion node*/
 void setClauseAssertion(ClauseId clause, Node node);

 /** Current assertion being converted and whether it is an input (rather than
  * a lemma) */
 void pushCurrentAssertion(Node assertion, bool isInput = false);
 void popCurrentAssertion();
 Node getCurrentAssertion();
 bool getCurrentAssertionKind();

 /**
  * Checks whether the assertion stack is empty.
  */
 bool isAssertionStackEmpty() const { return d_currentAssertionStack.empty(); }

 // accessors for the leaf assertions that are being converted to CNF
 Node getAssertionForClause(ClauseId clause);
};/* class CnfProof */

}  // namespace cvc5

#endif /* CVC5__CNF_PROOF_H */
