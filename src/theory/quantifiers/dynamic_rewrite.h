/*********************                                                        */
/*! \file dynamic_rewrite.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief dynamic_rewriter
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__DYNAMIC_REWRITER_H
#define CVC4__THEORY__QUANTIFIERS__DYNAMIC_REWRITER_H

#include <map>

#include "context/cdlist.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** DynamicRewriter
 *
 * This class is given a stream of equalities in calls to addRewrite(...).
 * The goal is to show that a subset of these can be inferred from previously
 * asserted equalities.  For example, a possible set of return values for
 * add rewrite on successive calls is the following:
 *
 *   addRewrite( x, y ) ---> true
 *   addRewrite( f( x ), f( y ) ) ---> false, since we already know x=y
 *   addRewrite( x, z ) ---> true
 *   addRewrite( x+y, x+z ) ---> false, since we already know y=x=z.
 *
 * This class can be used to filter out redundant candidate rewrite rules
 * when using the option sygusRewSynth().
 *
 * Currently, this class infers that an equality is redundant using
 * an instance of the equality engine that does congruence over all
 * operators by mapping all operators to uninterpreted ones and doing
 * congruence on APPLY_UF.
 *
 * TODO (#1591): Add more advanced technique, e.g. by theory rewriting
 * to show when terms can already be inferred equal.
 */
class DynamicRewriter
{
  typedef context::CDList<Node> NodeList;

 public:
  DynamicRewriter(const std::string& name, context::UserContext* u);
  ~DynamicRewriter() {}
  /** inform this class that the equality a = b holds. */
  void addRewrite(Node a, Node b);
  /**
   * Check whether this class knows that the equality a = b holds.
   */
  bool areEqual(Node a, Node b);
  /**
   * Convert node a to its internal representation, which replaces all
   * interpreted operators in a by a unique uninterpreted symbol.
   */
  Node toInternal(Node a);
  /**
   * Convert internal node ai to its original representation. It is the case
   * that toExternal(toInternal(a))=a. If ai is not a term returned by
   * toInternal, this method returns null.
   */
  Node toExternal(Node ai);

 private:
  /** index over argument types to function skolems
   *
   * The purpose of this trie is to associate a class of interpreted operator
   * with uninterpreted symbols. It is necessary to introduce multiple
   * uninterpreted symbols per interpreted operator since they may be
   * polymorphic. For example, for array select, its associate trie may look
   * like this:
   *   d_children[array_type_1]
   *     d_children[index_type_1] : k1
   *     d_children[index_type_2] : k2
   *   d_children[array_type_2]
   *     d_children[index_type_1] : k3
   */
  class OpInternalSymTrie
  {
   public:
    /**
     * Get the uninterpreted function corresponding to the top-most symbol
     * of the internal representation of term n. This will return a skolem
     * of the same type as n.getOperator() if it has one, or of the same type
     * as n itself otherwise.
     */
    Node getSymbol(Node n);

   private:
    /** the symbol at this node in the trie */
    Node d_sym;
    /** the children of this node in the trie */
    std::map<TypeNode, OpInternalSymTrie> d_children;
  };
  /** the internal operator symbol trie for this class */
  std::map<Node, OpInternalSymTrie> d_ois_trie;
  /** cache of the above function */
  std::map<Node, Node> d_term_to_internal;
  /** inverse of the above map */
  std::map<Node, Node> d_internal_to_term;
  /** stores congruence closure over terms given to this class. */
  eq::EqualityEngine d_equalityEngine;
  /** list of all equalities asserted to equality engine */
  NodeList d_rewrites;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__DYNAMIC_REWRITER_H */
