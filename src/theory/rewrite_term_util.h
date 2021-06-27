/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewrite term utilities
 */

#include "cvc5_private.h"

#ifndef CVC4__THEORY__REWRITE_TERM_UTIL__H
#define CVC4__THEORY__REWRITE_TERM_UTIL__H

#include <map>
#include <vector>

#include "expr/node.h"

namespace cvc5 {
namespace theory {

/** Mark variable as list */
void markListVar(TNode fv);
/** Is list variable */
bool isListVar(TNode fv);

/** Contains list variable */
bool containsListVar(TNode n);

/** get the null terminator */
Node getNullTerminator(Kind k, TypeNode tn);
/**
 * Substitution with list semantics 
 */
Node listSubstitute(Node src, std::vector<Node>& vars, std::vector< std::vector<Node > >& subs);

/**
 * Match with list semantics 
 */
bool listMatch(Node n1, Node n2, std::unordered_map<Node, std::vector<Node> >& subs);

}  // namespace theory
}  // namespace cvc5

#endif /* CVC4__REWRITER__TERM_UTIL__H */
