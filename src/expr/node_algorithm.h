/*********************                                                        */
/*! \file node_algorithm.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Common algorithms on nodes
 **
 ** This file implements common algorithms applied to nodes, such as checking if
 ** a node contains a free or a bound variable. This file should generally only
 ** be included in source files.
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__NODE_ALGORITHM_H
#define CVC4__EXPR__NODE_ALGORITHM_H

#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {
namespace expr {

/**
 * Check if the node n has a subterm t.
 * @param n The node to search in
 * @param t The subterm to search for
 * @param strict If true, a term is not considered to be a subterm of itself
 * @return true iff t is a subterm in n
 */
bool hasSubterm(TNode n, TNode t, bool strict = false);

/**
 * Check if the node n has >1 occurrences of a subterm t.
 */
bool hasSubtermMulti(TNode n, TNode t);

/**
 * @param k The kind of node to check
 * @param n The node to search in.
 * @return true iff there is a term in n that has kind k
 */
bool hasSubtermKind(Kind k, Node n);

/**
 * @param ks The kinds of node to check
 * @param n The node to search in.
 * @return true iff there is a term in n that has any kind ks
 */
bool hasSubtermKinds(const std::unordered_set<Kind, kind::KindHashFunction>& ks,
                     Node n);

/**
 * Check if the node n has a subterm that occurs in t.
 * @param n The node to search in
 * @param t The set of subterms to search for
 * @param strict If true, a term is not considered to be a subterm of itself
 * @return true iff there is a term in t that is a subterm in n
 */
bool hasSubterm(TNode n, const std::vector<Node>& t, bool strict = false);

/**
 * Returns true iff the node n contains a bound variable, that is a node of
 * kind BOUND_VARIABLE. This bound variable may or may not be free.
 * @param n The node under investigation
 * @return true iff this node contains a bound variable
 */
bool hasBoundVar(TNode n);

/**
 * Returns true iff the node n contains a free variable, that is, a node
 * of kind BOUND_VARIABLE that is not bound in n.
 * @param n The node under investigation
 * @return true iff this node contains a free variable.
 */
bool hasFreeVar(TNode n);

/**
 * Returns true iff the node n contains a closure, that is, a node
 * whose kind is FORALL, EXISTS, WITNESS, LAMBDA, or any other closure currently
 * supported.
 * @param n The node under investigation
 * @return true iff this node contains a closure.
 */
bool hasClosure(Node n);

/**
 * Get the free variables in n, that is, the subterms of n of kind
 * BOUND_VARIABLE that are not bound in n, adds these to fvs.
 * @param n The node under investigation
 * @param fvs The set which free variables are added to
 * @param computeFv If this flag is false, then we only return true/false and
 * do not add to fvs.
 * @return true iff this node contains a free variable.
 */
bool getFreeVariables(TNode n,
                      std::unordered_set<Node, NodeHashFunction>& fvs,
                      bool computeFv = true);

/**
 * Get all variables in n.
 * @param n The node under investigation
 * @param vs The set which free variables are added to
 * @return true iff this node contains a free variable.
 */
bool getVariables(TNode n, std::unordered_set<TNode, TNodeHashFunction>& vs);

/**
 * For term n, this function collects the symbols that occur as a subterms
 * of n. A symbol is a variable that does not have kind BOUND_VARIABLE.
 * @param n The node under investigation
 * @param syms The set which the symbols of n are added to
 */
void getSymbols(TNode n, std::unordered_set<Node, NodeHashFunction>& syms);

/**
 * For term n, this function collects the symbols that occur as a subterms
 * of n. A symbol is a variable that does not have kind BOUND_VARIABLE.
 * @param n The node under investigation
 * @param syms The set which the symbols of n are added to
 * @param visited A cache to be used for visited nodes.
 */
void getSymbols(TNode n,
                std::unordered_set<Node, NodeHashFunction>& syms,
                std::unordered_set<TNode, TNodeHashFunction>& visited);

/**
 * For term n, this function collects the operators that occur in n.
 * @param n The node under investigation
 * @param ops The map (from each type to operators of that type) which the
 * operators of n are added to
 */
void getOperatorsMap(
    TNode n,
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>& ops);

/**
 * For term n, this function collects the operators that occur in n.
 * @param n The node under investigation
 * @param ops The map (from each type to operators of that type) which the
 * operators of n are added to
 * @param visited A cache to be used for visited nodes.
 */
void getOperatorsMap(
    TNode n,
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>& ops,
    std::unordered_set<TNode, TNodeHashFunction>& visited);

/*
 * Substitution of Nodes in a capture avoiding way.
 * If x occurs free in n and it is substituted by a term t
 * and t includes some variable y that is bound in n,
 * then using alpha conversion y is replaced with a fresh bound variable
 * before the substitution.
 *
 */
Node substituteCaptureAvoiding(TNode n, Node src, Node dest);

/**
 * Same as substituteCaptureAvoiding above, but with a
 * simultaneous substitution of a vector of variables.
 * Elements in source will be replaced by their corresponding element in dest.
 * Both vectors should have the same size.
 */
Node substituteCaptureAvoiding(TNode n,
                               std::vector<Node>& src,
                               std::vector<Node>& dest);

/**
 * Get component types in type t. This adds all types that are subterms of t
 * when viewed as a term. For example, if t is (Array T1 T2), then
 * (Array T1 T2), T1 and T2 are component types of t.
 * @param t The type node under investigation
 * @param types The set which component types are added to.
 */
void getComponentTypes(
    TypeNode t, std::unordered_set<TypeNode, TypeNodeHashFunction>& types);

/** match
 *
 * Given two terms `n1` and `n2` containing free variables, match returns true
 * if `n2` is an instance of `n1`. In which case, `subs` is a mapping from the
 * free variables in `n1` to corresponding terms in `n2` such that:
 *
 * n1 * subs = n2 (where * denotes application of substitution).
 *
 * For example, given:
 * n1 = (+ a (* x 2)) (x denotes a free variable)
 * n2 = (+ a (* b 2))
 * a call to match should return `true` with subs = {(x, b)}
 *
 * @param n1 the term (containing free vars) to compare an instance term
 * against
 * @param n2 the instance term in question
 * @param subs the mapping from free vars in `n1` to terms in `n2`
 * @return whether or not `n2` is an instance of `n1`
 */
bool match(Node n1,
           Node n2,
           std::unordered_map<Node, Node, NodeHashFunction>& subs);

}  // namespace expr
}  // namespace CVC4

#endif
