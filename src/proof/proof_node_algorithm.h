/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
 * @return true if pn contains assumptions
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

/** Whether the result of a resolution corresponds to a singleton clause
 *
 * Viewing a node as a clause (i.e., as a list of literals), whether a node of
 * the form (or t1 ... tn) corresponds to the clause [t1, ..., tn]) or to the
 * clause [(or t1 ... tn)] can be ambiguous in different settings.
 *
 * This method determines whether a node `res`, corresponding to the result of a
 * resolution inference with premises `children` and arguments `args` (see
 * proof_rule.h for more details on the inference), is a singleton clause (i.e.,
 * a clause with a single literal).
 *
 * It does so relying on the fact that `res` is only a singleton if it occurs as
 * a child in one of the premises and is not eliminated afterwards. So we search
 * for `res` as a subterm of some child, which would mark its last insertion
 * into the resolution result. If `res` does not occur as the pivot to be
 * eliminated in a subsequent premise, then, and only then, it is a singleton
 * clause.
 *
 * @param res the result of a resolution inference
 * @param children the premises for the resolution inference
 * @param args the arguments, i.e., the pivots and their polarities, for the
 * resolution inference
 * @return whether `res` is a singleton clause
 */
bool isSingletonClause(TNode res,
                       const std::vector<Node>& children,
                       const std::vector<Node>& args);

}  // namespace expr
}  // namespace cvc5::internal

#endif /* CVC5__PROOF__PROOF_NODE_ALGORITHM_H */
