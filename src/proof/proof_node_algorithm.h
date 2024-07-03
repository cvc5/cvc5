/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof node algorithm utilities.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__PROOF_NODE_ALGORITHM_H
#define CVC5__PROOF__PROOF_NODE_ALGORITHM_H

#include <vector>

#include "cvc5/cvc5_proof_rule.h"
#include "expr/node.h"

namespace cvc5::internal {

class ProofNode;

namespace expr {

/**
 * This adds to the vector assump all formulas that are "free assumptions" of
 * the proof whose root is ProofNode pn. A free assumption is a formula F
 * that is an argument (in d_args) of a ProofNode whose kind is ASSUME, and
 * that proof node is not beneath an application of SCOPE containing F as an
 * argument.
 *
 * This traverses the structure of the dag represented by this ProofNode.
 * Its implementation is analogous to expr::getFreeVariables.
 *
 * @param pn The proof node.
 * @param assump The vector to add the free asumptions of pn to.
 */
void getFreeAssumptions(ProofNode* pn, std::vector<Node>& assump);
/**
 * Same as above, but maps assumptions to the proof pointer(s) for that
 * assumption. Notice that depending on how pn is constructed, there may be
 * multiple ProofNode that are ASSUME proofs of the same assumption, which
 * are each added to the range of the assumption.
 *
 * @param pn The proof node.
 * @param amap The mapping to add the free asumptions of pn and their
 * corresponding proof nodes to.
 */
void getFreeAssumptionsMap(
    std::shared_ptr<ProofNode> pn,
    std::map<Node, std::vector<std::shared_ptr<ProofNode>>>& amap);

/**
 * Get the subproofs of pn that have rule r.
 * @param pn The proof node.
 * @param r The rule to find.
 * @param pfs The list of subproofs of pn that have rule r.
 */
void getSubproofRule(std::shared_ptr<ProofNode> pn,
                     ProofRule r,
                     std::vector<std::shared_ptr<ProofNode>>& pfs);

/**
 * Return true if pn contains a subproof whose rule is ASSUME. Notice that we
 * do *not* distinguish between free vs. non-free assumptions in this call.
 * This call involves at most a single dag traversal over the proof node.
 *
 * This call will partially populate caMap. In particular, it will only fill
 * caMap for the proof nodes that were traversed up to where the first
 * assumption in pn was found.
 *
 * @param pn The proof node.
 * @param caMap Cache of results, mapping proof nodes to whether they contain
 * assumptions.
 * @param allowed The set of assumptions the proof is allowed to contain, i.e.
 * if the free assumptions of pn is a subset of this set, we return false.
 * @return true if pn contains assumptions (not in allowed).
 */
bool containsAssumption(const ProofNode* pn,
                        std::unordered_map<const ProofNode*, bool>& caMap,
                        const std::unordered_set<Node>& allowed);
/**
 * Same as above, but with an empty set of allowed assumptions.
 */
bool containsAssumption(const ProofNode* pn,
                        std::unordered_map<const ProofNode*, bool>& caMap);
/**
 * Same as above, with an empty cache as the initial value of caMap.
 */
bool containsAssumption(const ProofNode* pn);

/**
 * @return true if pn contains pnc.
 */
bool containsSubproof(ProofNode* pn, ProofNode* pnc);

/**
 * Same as above, with a visited cache.
 *
 * @return true if pn contains pnc.
 */
bool containsSubproof(ProofNode* pn,
                      ProofNode* pnc,
                      std::unordered_set<const ProofNode*>& visited);

/**
 * Returns the ProofRule that handles congruence for the given term.
 *
 * @param n The term, i.e. the lhs or rhs of the conclusion of the cong step.
 * @param args The arguments to the application of cong for the given term
 * @return the proof rule for congruence over the given term, which is one
 * of CONG, NARY_CONG or HO_CONG.
 */
ProofRule getCongRule(const Node& n, std::vector<Node>& args);

}  // namespace expr
}  // namespace cvc5::internal

#endif /* CVC5__PROOF__PROOF_NODE_ALGORITHM_H */
