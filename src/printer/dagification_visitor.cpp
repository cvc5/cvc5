/*********************                                                        */
/*! \file dagification_visitor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andres Noetzli, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of a dagifier for CVC4 expressions
 **
 ** Implementation of a dagifier for CVC4 expressions.
 **/

#include "printer/dagification_visitor.h"

#include "context/context.h"
#include "expr/node_algorithm.h"
#include "expr/node_manager_attributes.h"
#include "theory/substitutions.h"

#include <sstream>

namespace CVC4 {
namespace printer {

DagificationVisitor::DagificationVisitor(unsigned threshold,
                                         std::string letVarPrefix)
    : d_threshold(threshold),
      d_letVarPrefix(letVarPrefix),
      d_nodeCount(),
      d_reservedLetNames(),
      d_top(),
      d_context(new context::Context()),
      d_substitutions(new theory::SubstitutionMap(d_context)),
      d_letVar(0),
      d_done(false),
      d_uniqueParent(),
      d_substNodes()
{
  // 0 doesn't make sense
  AlwaysAssertArgument(threshold > 0, threshold);
}

DagificationVisitor::~DagificationVisitor() {
  delete d_substitutions;
  delete d_context;
}

bool DagificationVisitor::alreadyVisited(TNode current, TNode parent) {
  Kind ck = current.getKind();
  if (current.isClosure())
  {
    // for quantifiers, we visit them but we don't recurse on them
    visit(current, parent);

    // search for variables that start with the let prefix
    std::unordered_set<TNode, TNodeHashFunction> vs;
    expr::getVariables(current, vs);
    for (const TNode v : vs)
    {
      const std::string name = v.getAttribute(expr::VarNameAttr());
      if (name.compare(0, d_letVarPrefix.size(), d_letVarPrefix) == 0)
      {
        d_reservedLetNames.insert(name);
      }
    }
    return true;
  }
  else if (current.isVar())
  {
    const std::string name = current.getAttribute(expr::VarNameAttr());
    if (name.compare(0, d_letVarPrefix.size(), d_letVarPrefix) == 0)
    {
      d_reservedLetNames.insert(name);
    }
  }
  // don't visit variables, constants, or those exprs that we've
  // already seen more than the threshold: if we've increased
  // the count beyond the threshold already, we've done the same
  // for all subexpressions, so it isn't useful to traverse and
  // increment again (they'll be dagified anyway).
  return current.isVar() || current.getMetaKind() == kind::metakind::CONSTANT
         || current.getNumChildren() == 0
         || ((ck == kind::NOT || ck == kind::UMINUS)
             && (current[0].isVar()
                 || current[0].getMetaKind() == kind::metakind::CONSTANT))
         || ck == kind::SORT_TYPE || d_nodeCount[current] > d_threshold;
}

void DagificationVisitor::visit(TNode current, TNode parent) {

#ifdef CVC4_TRACING
#  ifdef CVC4_DEBUG
  // turn off dagification for Debug stream while we're doing this work
  Node::dag::Scope scopeDebug(Debug.getStream(), false);
#  endif /* CVC4_DEBUG */
  // turn off dagification for Trace stream while we're doing this work
  Node::dag::Scope scopeTrace(Trace.getStream(), false);
#endif /* CVC4_TRACING */

  if(d_uniqueParent.find(current) != d_uniqueParent.end()) {
    // we've seen this expr before

    TNode& uniqueParent = d_uniqueParent[current];

    // We restrict this optimization to nodes with arity 1 since otherwise we
    // may run into issues with tree traverals. Without this restriction
    // dumping regress3/pp-regfile increases the file size by a factor of 5000.
    if (!uniqueParent.isNull()
        && (uniqueParent != parent || parent.getNumChildren() > 1))
    {
      // there is not a unique parent for this expr, mark it
      uniqueParent = TNode::null();
    }

    // increase the count
    const unsigned count = ++d_nodeCount[current];

    if(count > d_threshold) {
      // candidate for a let binder
      d_substNodes.push_back(current);
    }
  } else {
    // we haven't seen this expr before
    Assert(d_nodeCount[current] == 0);
    d_nodeCount[current] = 1;
    d_uniqueParent[current] = parent;
  }
}

void DagificationVisitor::start(TNode node) {
  AlwaysAssert(!d_done) << "DagificationVisitor cannot be re-used";
  d_top = node;
}

void DagificationVisitor::done(TNode node) {
  AlwaysAssert(!d_done);

  d_done = true;

#ifdef CVC4_TRACING
#  ifdef CVC4_DEBUG
  // turn off dagification for Debug stream while we're doing this work
  Node::dag::Scope scopeDebug(Debug.getStream(), false);
#  endif /* CVC4_DEBUG */
  // turn off dagification for Trace stream while we're doing this work
  Node::dag::Scope scopeTrace(Trace.getStream(), false);
#endif /* CVC4_TRACING */

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

    // construct the let binder
    std::stringstream ss;
    do
    {
      ss.str("");
      ss << d_letVarPrefix << d_letVar++;
    } while (d_reservedLetNames.find(ss.str()) != d_reservedLetNames.end());
    Node letvar = NodeManager::currentNM()->mkSkolem(ss.str(), (*i).getType(), "dagification", NodeManager::SKOLEM_NO_NOTIFY | NodeManager::SKOLEM_EXACT_NAME);

    // apply previous substitutions to the rhs, enabling cascading LETs
    Node n = d_substitutions->apply(*i);
    Assert(!d_substitutions->hasSubstitution(n));
    d_substitutions->addSubstitution(n, letvar);
  }
}

const theory::SubstitutionMap& DagificationVisitor::getLets() {
  AlwaysAssert(d_done)
      << "DagificationVisitor must be used as a visitor before "
         "getting the dagified version out!";
  return *d_substitutions;
}

Node DagificationVisitor::getDagifiedBody() {
  AlwaysAssert(d_done)
      << "DagificationVisitor must be used as a visitor before "
         "getting the dagified version out!";

#ifdef CVC4_TRACING
#  ifdef CVC4_DEBUG
  // turn off dagification for Debug stream while we're doing this work
  Node::dag::Scope scopeDebug(Debug.getStream(), false);
#  endif /* CVC4_DEBUG */
  // turn off dagification for Trace stream while we're doing this work
  Node::dag::Scope scopeTrace(Trace.getStream(), false);
#endif /* CVC4_TRACING */

  return d_substitutions->apply(d_top);
}

}/* CVC4::printer namespace */
}/* CVC4 namespace */
