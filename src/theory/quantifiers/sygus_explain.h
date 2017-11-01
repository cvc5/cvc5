/*********************                                                        */
/*! \file sygus_explain.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus explanations
 **/

#include "cvc4_private.h"

#ifndef __CVC4__SYGUS_EXPLAIN_H
#define __CVC4__SYGUS_EXPLAIN_H

#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Recursive term builder
 *
 * This is a utility used to generate variants
 * of a term n, where subterms of n can be replaced
 * by others via calls to replaceChild(...).
 *
 * This class maintains a "context", which indicates
 * a position in term n. Below, we call the subterm of
 * the initial term n at this position the "active term".
 *
 */
class TermRecBuild
{
 public:
  TermRecBuild() {}
  /** set the initial term to n
   *
   * The context initially empty, that is,
   * the active term is initially n.
   */
  void init(Node n);
  /** push the context
   *
   * This updates the context so that the
   * active term is updated to curr[p], where
   * curr is the previously active term.
   */
  void push(unsigned p);
  /** pop the context */
  void pop();
  /** indicates that the i^th child of the active
   * term should be replaced by r in calls to build().
   */
  void replaceChild(unsigned i, Node r);
  /** get the i^th child of the active term */
  Node getChild(unsigned i);
  /** build the (modified) version of the term
   * we intialized via the call to init().
   */
  Node build(unsigned p = 0);

 private:
  /** stack of active terms */
  std::vector<Node> d_term;
  /** stack of children of active terms
   * Notice that these may be modified with calls to replaceChild(...).
   */
  std::vector<std::vector<Node> > d_children;
  /** stack the kind of active terms */
  std::vector<Kind> d_kind;
  /** stack of whether the active terms had an operator */
  std::vector<bool> d_has_op;
  /** stack of positions that were pushed via calls to push(...) */
  std::vector<unsigned> d_pos;
  /** add term to the context stack */
  void addTerm(Node n);
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__SYGUS_INVARIANCE_H */
