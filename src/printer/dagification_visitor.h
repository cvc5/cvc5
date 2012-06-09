/*********************                                                        */
/*! \file dagification_visitor.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011, 2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PRINTER__DAGIFICATION_VISITOR_H
#define __CVC4__PRINTER__DAGIFICATION_VISITOR_H

#include "context/context.h"
#include "theory/substitutions.h"
#include "expr/node.h"
#include "util/hash.h"

#include <vector>
#include <string>
#include <sstream>

namespace CVC4 {
namespace printer {

class DagificationVisitor {

  unsigned d_threshold;
  std::string d_letVarPrefix;
  std::hash_map<TNode, unsigned, TNodeHashFunction> d_nodeCount;
  TNode d_top;
  context::Context* d_context;
  theory::SubstitutionMap* d_substitutions;
  unsigned d_letVar;
  bool d_done;
  std::hash_map<TNode, TNode, TNodeHashFunction> d_uniqueParent;
  std::vector<TNode> d_substNodes;

public:

  typedef void return_type;

  DagificationVisitor(unsigned threshold, std::string letVarPrefix = "_let_") :
    d_threshold(threshold),
    d_letVarPrefix(letVarPrefix),
    d_nodeCount(),
    d_top(),
    d_context(new context::Context()),
    d_substitutions(new theory::SubstitutionMap(d_context)),
    d_letVar(0),
    d_done(false),
    d_uniqueParent(),
    d_substNodes() {

    // 0 doesn't make sense
    CheckArgument(threshold > 0, threshold);
  }

  ~DagificationVisitor() {
    delete d_substitutions;
    delete d_context;
  }

  /**
   * Returns true if current has already been dagified.
   */
  bool alreadyVisited(TNode current, TNode parent) {
    // don't visit variables, constants, or those exprs that we've
    // already seen more than the threshold: if we've increased
    // the count beyond the threshold already, we've done the same
    // for all subexpressions, so it isn't useful to traverse and
    // increment again (they'll be dagified anyway).
    return current.getMetaKind() == kind::metakind::VARIABLE ||
           current.getMetaKind() == kind::metakind::CONSTANT ||
           ( ( current.getKind() == kind::NOT ||
               current.getKind() == kind::UMINUS ) &&
             ( current[0].getMetaKind() == kind::metakind::VARIABLE ||
               current[0].getMetaKind() == kind::metakind::CONSTANT ) ) ||
           current.getKind() == kind::SORT_TYPE ||
           d_nodeCount[current] > d_threshold;
  }

  /**
   * Dagify the "current" expression.
   */
  void visit(TNode current, TNode parent) {
    if(d_uniqueParent.find(current) != d_uniqueParent.end()) {
      TNode& uniqueParent = d_uniqueParent[current];

      if(!uniqueParent.isNull() && uniqueParent != parent) {
        // there is not a unique parent for this expr
        uniqueParent = TNode::null();
      }

      unsigned count = ++d_nodeCount[current];

      if(count > d_threshold) {
        d_substNodes.push_back(current);
      }
    } else {
      Assert(d_nodeCount[current] == 0);
      d_nodeCount[current] = 1;
      d_uniqueParent[current] = parent;
    }
  }

  /**
   * Marks the node as the starting literal.
   */
  void start(TNode node) {
    Assert(!d_done, "DagificationVisitor cannot be re-used");
    d_top = node;
  }

  /**
   * Called when we're done with all visitation.
   */
  void done(TNode node) {
    Assert(!d_done);

    d_done = true;

    // letify subexprs before parents (cascading LETs)
    std::sort(d_substNodes.begin(), d_substNodes.end());

    for(std::vector<TNode>::iterator i = d_substNodes.begin();
        i != d_substNodes.end();
        ++i) {
      Assert(d_nodeCount[*i] > d_threshold);
      TNode parent = d_uniqueParent[*i];
      if(!parent.isNull() && d_nodeCount[parent] > d_threshold) {
        // no need to letify this expr, because it only occurs in
        // a single super-expression, and that one will be letified
        continue;
      }

      std::stringstream ss;
      ss << d_letVarPrefix << d_letVar++;
      Node letvar = NodeManager::currentNM()->mkVar(ss.str(), (*i).getType());

      Node n = d_substitutions->apply(*i);
      // the three last arguments to addSubstitution are:
      // invalidateCache -- the rhs of our substitution is a letvar,
      //   we're not going to use it on lhs so no cache problem
      // backSub - no need for SubstitutionMap to do internal substitution,
      //   we did our own above
      // forwardSub - ditto
      Assert(! d_substitutions->hasSubstitution(n));
      d_substitutions->addSubstitution(n, letvar);
    }
  }

  /**
   * Get the let substitutions.
   */
  const theory::SubstitutionMap& getLets() {
    Assert(d_done, "DagificationVisitor must be used as a visitor before getting the dagified version out!");
    return *d_substitutions;
  }

  /**
   * Return the let-substituted expression.
   */
  Node getDagifiedBody() {
    Assert(d_done, "DagificationVisitor must be used as a visitor before getting the dagified version out!");
    return d_substitutions->apply(d_top);
  }

};/* class DagificationVisitor */

}/* CVC4::printer namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PRINTER__DAGIFICATION_VISITOR_H */
