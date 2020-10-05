/*********************                                                        */
/*! \file dagification_visitor.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andres Noetzli, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A dagifier for CVC4 expressions
 **
 ** A dagifier for CVC4 expressions.
 **/

#include "cvc4_private.h"

#ifndef CVC4__PRINTER__DAGIFICATION_VISITOR_H
#define CVC4__PRINTER__DAGIFICATION_VISITOR_H

#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "util/hash.h"

namespace CVC4 {

namespace context {
  class Context;
}/* CVC4::context namespace */

namespace theory {
  class SubstitutionMap;
}/* CVC4::theory namespace */

namespace printer {

/**
 * This is a visitor class (intended to be used with CVC4's NodeVisitor)
 * that visits an expression looking for common subexpressions that appear
 * more than N times, where N is a configurable threshold.  Afterward,
 * let bindings can be extracted from this visitor and applied to the
 * expression.
 *
 * This dagifier never introduces let bindings for variables, constants,
 * unary-minus exprs over variables or constants, or NOT exprs over
 * variables or constants.  This dagifier never introduces let bindings
 * for types.
 */
class DagificationVisitor {

  /**
   * The threshold for dagification.  Subexprs occurring more than this
   * number of times are dagified.
   */
  const unsigned d_threshold;

  /**
   * The prefix for introduced let bindings.
   */
  const std::string d_letVarPrefix;

  /**
   * A map of subexprs to their occurrence count.
   */
  std::unordered_map<TNode, unsigned, TNodeHashFunction> d_nodeCount;

  /**
   * The set of variable names with the let prefix that appear in the
   * expression.
   */
  std::unordered_set<std::string> d_reservedLetNames;

  /**
   * The top-most node we are visiting.
   */
  TNode d_top;

  /**
   * This class doesn't operate in a context-dependent fashion, but
   * SubstitutionMap does, so we need a context.
   */
  context::Context* d_context;

  /**
   * A map of subexprs to their newly-introduced let bindings.
   */
  theory::SubstitutionMap* d_substitutions;

  /**
   * The current count of let bindings.  Used to build unique names
   * for the bindings.
   */
  unsigned d_letVar;

  /**
   * Keep track of whether we are done yet (for assertions---this visitor
   * can only be used one time).
   */
  bool d_done;

  /**
   * If a subexpr occurs uniquely in one parent expr, this map points to
   * it.  An expr not occurring as a key in this map means we haven't
   * seen it yet (and its occurrence count should be zero).  If an expr
   * points to the null expr in this map, it means we've seen more than
   * one parent, so the subexpr doesn't have a unique parent.
   *
   * This information is kept because if a subexpr occurs more than the
   * threshold, it is normally subject to dagification.  But if it occurs
   * only in one unique parent expression, and the parent meets the
   * threshold too, then the parent will be dagified and there's no point
   * in independently dagifying the child.  (If it is beyond the threshold
   * and occurs in more than one parent, we'll independently dagify.)
   */
  std::unordered_map<TNode, TNode, TNodeHashFunction> d_uniqueParent;

  /**
   * A list of all nodes that meet the occurrence threshold and therefore
   * *may* be subject to dagification, except for the unique-parent rule
   * mentioned above.
   */
  std::vector<TNode> d_substNodes;

public:

  /** Our visitor doesn't return anything. */
  typedef void return_type;

  /**
   * Construct a dagification visitor with the given threshold and let
   * binding prefix.
   *
   * @param threshold the threshold to apply for dagification (must be > 0)
   * @param letVarPrefix prefix for let bindings (by default, "_let_")
   */
  DagificationVisitor(unsigned threshold, std::string letVarPrefix = "_let_");

  /**
   * Simple destructor, clean up memory.
   */
  ~DagificationVisitor();

  /**
   * Returns true if "current" has already been visited a sufficient
   * number of times to make it a candidate for dagification, or if
   * it cannot ever be subject to dagification.
   */
  bool alreadyVisited(TNode current, TNode parent);

  /**
   * Visit the expr "current", it might be a candidate for a let binder.
   */
  void visit(TNode current, TNode parent);

  /**
   * Marks the node as the starting literal.
   */
  void start(TNode node);

  /**
   * Called when we're done with all visitation.  Does postprocessing.
   */
  void done(TNode node);

  /**
   * Get the let substitutions.
   */
  const theory::SubstitutionMap& getLets();

  /**
   * Return the let-substituted expression.
   */
  Node getDagifiedBody();

};/* class DagificationVisitor */

}/* CVC4::printer namespace */
}/* CVC4 namespace */

#endif /* CVC4__PRINTER__DAGIFICATION_VISITOR_H */
