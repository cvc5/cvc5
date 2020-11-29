/*********************                                                        */
/*! \file alpha_equivalence.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Alpha equivalence checking
 **/

#include "cvc4_private.h"

#ifndef CVC4__ALPHA_EQUIVALENCE_H
#define CVC4__ALPHA_EQUIVALENCE_H

#include "theory/quantifiers/quant_util.h"

#include "expr/term_canonize.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/**
 * This is a discrimination tree index for terms. It handles variadic
 * operators by indexing based on operator arity, and flattens multiple
 * occurrences of subterms.
 *
 * For example, the term
 * +( f( x ), +( a, f(x), b ) )
 *   is stored at:
 * d_children[+][2].d_children[f][1].
 *   d_children[x][0].d_children[+][3].
 *     d_children[a][0].d_children[f(x)][0].
 *       d_children[b][0]
 * Notice that the second occurrence of f(x) is flattened.
 */
class AlphaEquivalenceNode {
public:
 /** children of this node */
 std::map<Node, std::map<int, AlphaEquivalenceNode> > d_children;
 /** the data at this node */
 Node d_quant;
 /** Registers term q to this trie. The term t is the canonical form of q. */
 Node registerNode(Node q, Node t);
};

/**
 * This trie stores a trie of the above form for each multi-set of types. For
 * each term t registered to this node, we store t in the appropriate
 * AlphaEquivalenceNode trie. For example, if t contains 2 free variables
 * of type T1 and 3 free variables of type T2, then it is stored at
 * d_children[T1][2].d_children[T2][3].
 */
class AlphaEquivalenceTypeNode {
public:
 /** children of this node */
 std::map<TypeNode, std::map<int, AlphaEquivalenceTypeNode> > d_children;
 /** the database of terms at this node */
 AlphaEquivalenceNode d_data;
 /** register node
  *
  * This registers term q to this trie. The term t is the canonical form of
  * q, typs/typ_count represent a multi-set of types of free variables in t.
  */
 Node registerNode(Node q,
                   Node t,
                   std::vector<TypeNode>& typs,
                   std::map<TypeNode, int>& typ_count);
};

/**
 * Stores a database of quantified formulas, which computes alpha-equivalence.
 */
class AlphaEquivalenceDb
{
 public:
  AlphaEquivalenceDb(expr::TermCanonize* tc) : d_tc(tc) {}
  /** adds quantified formula q to this database
   *
   * This function returns a quantified formula q' that is alpha-equivalent to
   * q. If q' != q, then q' was previously added to this database via a call
   * to addTerm.
   */
  Node addTerm(Node q);

 private:
  /** a trie per # of variables per type */
  AlphaEquivalenceTypeNode d_ae_typ_trie;
  /** pointer to the term canonize utility */
  expr::TermCanonize* d_tc;
};

/**
 * A quantifiers module that computes reductions based on alpha-equivalence,
 * using the above utilities.
 */
class AlphaEquivalence
{
 public:
  AlphaEquivalence(QuantifiersEngine* qe);
  ~AlphaEquivalence(){}
  /** reduce quantifier
   *
   * If non-null, its return value is lemma justifying why q is reducible.
   * This is of the form ( q = q' ) where q' is a quantified formula that
   * was previously registered to this class via a call to reduceQuantifier,
   * and q and q' are alpha-equivalent.
   */
  Node reduceQuantifier( Node q );

 private:
  /** the database of quantified formulas registered to this class */
  AlphaEquivalenceDb d_aedb;
};

}
}
}

#endif
