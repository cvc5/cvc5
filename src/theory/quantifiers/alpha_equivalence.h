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
 * This trie stores a trie of the above form for each multi-set of types. For
 * each term t registered to this node, we store t in the appropriate
 * AlphaEquivalenceNode trie. For example, if t contains 2 free variables
 * of type T1 and 3 free variables of type T2, then it is stored at
 * d_children[T1][2].d_children[T2][3].
 */
class AlphaEquivalenceTypeNode {
public:
 /** children of this node */
 std::map<std::pair<TypeNode, size_t>, AlphaEquivalenceTypeNode> d_children;
 /**
  * map from canonized quantifier bodies to a quantified formula whose
  * canonized body is that term.
  */
 std::map<Node, Node> d_quant;
 /** register node
  *
  * This registers term q to this trie. The term t is the canonical form of
  * q, typs/typCount represent a multi-set of types of free variables in t.
  */
 Node registerNode(Node q,
                   Node t,
                   std::vector<TypeNode>& typs,
                   std::map<TypeNode, size_t>& typCount);
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
  /** a term canonizer */
  expr::TermCanonize d_termCanon;
  /** the database of quantified formulas registered to this class */
  AlphaEquivalenceDb d_aedb;
};

}
}
}

#endif
