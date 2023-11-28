/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for resolution proofs.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__RESOLUTION_PROOFS_UTIL_H
#define CVC5__PROOF__RESOLUTION_PROOFS_UTIL_H

#include <vector>

#include "expr/node.h"

namespace cvc5::internal {

class CDProof;
class ProofNodeManager;

namespace proof {

/**
 * When given children and args lead to different sets of literals in a
 * conclusion depending on whether macro resolution or chain resolution is
 * applied, the literals that appear in the chain resolution result, but not
 * in the macro resolution result, from now on "crowding literals", are
 * literals removed implicitly by macro resolution. For example
 *
 *      l0 v l0 v l0 v l1 v l2    ~l0 v l1   ~l1
 * (1)  ----------------------------------------- MACRO_RES
 *                 l2
 *
 * but
 *
 *      l0 v l0 v l0 v l1 v l2    ~l0 v l1   ~l1
 * (2)  ---------------------------------------- CHAIN_RES
 *                l0 v l0 v l1 v l2
 *
 * where l0 and l1 are crowding literals in the second proof.
 *
 * There are two views for how MACRO_RES implicitly removes the crowding
 * literal, i.e., how MACRO_RES can be expanded into CHAIN_RES so that
 * crowding literals are removed. The first is that (1) becomes
 *
 *  l0 v l0 v l0 v l1 v l2  ~l0 v l1  ~l0 v l1  ~l0 v l1  ~l1  ~l1  ~l1  ~l1
 *  ---------------------------------------------------------------- CHAIN_RES
 *                                 l2
 *
 * via the repetition of the premise responsible for removing more than one
 * occurrence of the crowding literal. The issue however is that this
 * expansion is exponential. Note that (2) has two occurrences of l0 and one
 * of l1 as crowding literals. However, by repeating ~l0 v l1 two times to
 * remove l0, the clause ~l1, which would originally need to be repeated only
 * one time, now has to be repeated two extra times on top of that one. With
 * multiple crowding literals and their elimination depending on premises that
 * themselves add crowding literals one can easily end up with resolution
 * chains going from dozens to thousands of premises. Such examples do occur
 * in practice, even in our regressions.
 *
 * The second way of expanding MACRO_RES, which avoids this exponential
 * behavior, is so that (1) becomes
 *
 *      l0 v l0 v l0 v l1 v l2
 * (4)  ---------------------- FACTORING
 *      l0 v l1 v l2                       ~l0 v l1
 *      ------------------------------------------- CHAIN_RES
 *                   l1 v l1 v l2
 *                  ------------- FACTORING
 *                     l1 v l2                   ~l1
 *                    ------------------------------ CHAIN_RES
 *                                 l2
 *
 * This method first determines what are the crowding literals by checking
 * what literals occur in clauseLits that do not occur in targetClauseLits
 * (the latter contains the literals from the original MACRO_RES conclusion
 * while the former the literals from a direct application of CHAIN_RES). Then
 * it builds a proof such as (4) and adds the steps to cdp. The final
 * conclusion is returned.
 *
 * Note that in the example the CHAIN_RES steps introduced had only two
 * premises, and could thus be replaced by a RESOLUTION step, but since we
 * general there can be more than two premises we always use CHAIN_RES.
 *
 * Note that when reorderPremises is true we will (potentially)
 * reorder the premises so that the clauses eliminating crowding literals are
 * moved further down the chain (when it is safe to do so), so that the number
 * of breaks introduced to the chain, as illustrated above, is minimized.
 *
 * @param reorderPremises Whether to optimize elemination by reordering premises
 * @param clauseLits literals in the conclusion of a CHAIN_RESOLUTION step
 * with children and args[1:]
 * @param clauseLits literals in the conclusion of a MACRO_RESOLUTION step
 * with children and args
 * @param children a list of clauses
 * @param args a list of arguments to a MACRO_RESOLUTION step
 * @param cdp a CDProof
 * @return The resulting node of transforming MACRO_RESOLUTION into
 * CHAIN_RESOLUTION according to the above idea.
 */
Node eliminateCrowdingLits(bool reorderPremises,
                           const std::vector<Node>& clauseLits,
                           const std::vector<Node>& targetClauseLits,
                           const std::vector<Node>& children,
                           const std::vector<Node>& args,
                           CDProof* cdp,
                           ProofNodeManager* pnm);

/** Whether the result of a resolution corresponds to a singleton clause
 *
 * Viewing a node as a clause (i.e., as a list of literals), whether a node of
 * the form (or t1 ... tn) corresponds to the clause [t1, ..., tn]) or to the
 * clause [(or t1 ... tn)] can be ambiguous in different settings.
 *
 * This method determines whether a node `res`, corresponding to the result of
 * a resolution inference with premises `children` and arguments `args` (see
 * proof_rule.h for more details on the inference), is a singleton clause
 * (i.e., a clause with a single literal).
 *
 * It does so relying on the fact that `res` is only a singleton if it occurs
 * as a child in one of the premises and is not eliminated afterwards. So we
 * search for `res` as a subterm of some child, which would mark its last
 * insertion into the resolution result. If `res` does not occur as the pivot
 * to be eliminated in a subsequent premise, then, and only then, it is a
 * singleton clause.
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

}  // namespace proof
}  // namespace cvc5::internal

#endif
