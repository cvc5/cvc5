/*********************                                                        */
/*! \file quantifier_macro_elimination.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Scott Kovach, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief TODO add summary
 **
 ** TODO
 **    main TODOs:
 **    - handle nontrivial arithmetic (see solveInEquality)
 **/
#include "preprocessing/passes/quantifier_macro_elimination.h"

#include "smt/smt_statistics_registry.h"
#include "theory/logic_info.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace std;
using namespace CVC4::theory;
using namespace CVC4::kind;

QuantifierMacroElimination::QuantifierMacroElimination(
    PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "quantifier-macro-elimination")
{
}

QuantifierMacroElimination::~QuantifierMacroElimination() {}

// Check that arguments of application are unique bound variables and return
// them in arguments. Assumes application is an APPLY_UF node.
bool getApplicationVariableArgumentsIfUnique(Node application,
                                             vector<Node>& arguments)
{
  std::set<Node> seenVars;
  for (size_t i = 0; i < application.getNumChildren(); ++i)
  {
    Node arg = application[i];
    // to be part of a macro definition, application must be well-typed and
    // refer to unique bound variables
    if (arg.getKind() != BOUND_VARIABLE)
    {
      return false;
    }
    if (setContains(seenVars, arg))
    {
      return false;
    }
    seenVars.insert(arg);
  }
  arguments = vector<Node>(seenVars.begin(), seenVars.end());
  return true;
}

// If the definition contains a reference to predicate, or a reference to any
// earlier defined macro, it is not valid
bool QuantifierMacroElimination::isDefinitionValid(Node predicate,
                                                   Node definition)
{
  // traverse definition and check for occurrence of predicate
  vector<Node> stack;
  stack.push_back(definition);
  while (stack.size() > 0)
  {
    Node current = stack.back();
    stack.pop_back();
    if (current.getKind() == APPLY_UF)
    {
      Node currentOperator = current.getOperator();
      if (currentOperator == predicate)
      {
        return false;
      }
      if (mapContains(d_macroDefinitions, currentOperator))
      {
        return false;
      }
    }
    for (size_t i = 0; i < current.getNumChildren(); ++i)
    {
      stack.push_back(current[i]);
    }
  }
  return true;
}

// Returns true if a macro definition is derived from the input
bool QuantifierMacroElimination::addMacroDefinitionIfPresent(Node assertion)
{
  Trace("QME:all") << "checking " << assertion << endl;
  if (assertion.getKind() == FORALL)
  {
    if (assertion[1].getKind() == EQUAL)
    {
      Node equality_node = assertion[1];
      // handle phi(X) = P X definition by swapping argument order
      if (equality_node[1].getKind() == APPLY_UF)
      {
        equality_node = NodeManager::currentNM()->mkNode(
            kind::EQUAL, equality_node[1], equality_node[0]);
      }
      if (equality_node[0].getKind() == APPLY_UF)
      {
        // TODO check that free variables \subset assertion[0]
        //   question: how would this not be the case given that we're in a top
        //   level assertion?
        Node application = equality_node[0];
        vector<Node> application_children;
        // adds arguments of UF to application_children
        if (!getApplicationVariableArgumentsIfUnique(application,
                                                     application_children))
        {
          Trace("QME:all")
              << "application is not applied to unique variable list"
              << equality_node << endl;
          return false;
        }
        Node predicate = application.getOperator();
        Node definition = equality_node[1];
        if (!isDefinitionValid(predicate, definition))
        {
          Trace("QME") << "definition recursively references predicate or "
                          "earlier macro, skipping"
                       << endl;
          return false;
        }
        Trace("QME") << "found definition:\n  " << predicate
                     << " := " << definition << endl;
        d_macroDefinitions[predicate] = definition;
        d_macroBoundVariables[predicate] = application_children;
        // don't bother rewriting in definition node
        d_definitionNodes.insert(application);
        return true;
      }
    }
  }
  return false;
}

Node QuantifierMacroElimination::replaceMacroInstances(Node n)
{
  Trace("QME:all") << "replaceMacroInstances: " << n << endl;
  if (setContains(d_definitionNodes, n))
  {
    Trace("QME:all") << "skipping: " << n << endl;
    return n;
  }
  vector<Node> children;
  for (size_t i = 0; i < n.getNumChildren(); ++i)
  {
    children.push_back(n[i]);
  }
  if (n.getKind() == APPLY_UF)
  {
    Node predicate = n.getOperator();
    if (d_macroDefinitions.find(predicate) != d_macroDefinitions.end())
    {
      Node macroDefinition = d_macroDefinitions[predicate];
      vector<Node> macro_variables = d_macroBoundVariables[predicate];
      Trace("QME") << "applying substitution for\n  " << n << endl;
      Node new_node = macroDefinition.substitute(macro_variables.begin(),
                                                 macro_variables.end(),
                                                 children.begin(),
                                                 children.end());
      Trace("QME") << "rewritten node: " << new_node << endl;
      return new_node;
    }
    else
    {
      return n;
    }
  }
  else
  {
    vector<Node> newChildren;
    if (n.getNumChildren() > 0)
    {
      bool anyChildChanged = false;
      for (size_t i = 0; i < n.getNumChildren(); ++i)
      {
        // TODO check if any changed
        Node newChild = replaceMacroInstances(n[i]);
        newChildren.push_back(newChild);
        anyChildChanged = anyChildChanged || newChild != n[i];
      }
      if (anyChildChanged)
      {
        if (n.getMetaKind() == metakind::PARAMETERIZED)
        {
          newChildren.insert(newChildren.begin(), n.getOperator());
        }
        return NodeManager::currentNM()->mkNode(n.getKind(), newChildren);
      }
      else
      {
        return n;
      }
    }
    else
    {
      return n;
    }
  }
}

PreprocessingPassResult QuantifierMacroElimination::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  d_preprocContext->spendResource(ResourceManager::Resource::PreprocessStep);

  vector<Node>& assertions = assertionsToPreprocess->ref();
  vector<Node> macroAssertions;
  // Find macro definitions:
  for (Node& assertion : assertions)
  {
    bool addedDefinition = addMacroDefinitionIfPresent(assertion);
    PROOF(if (addedDefinition) { macroAssertions.push_back(assertion); });
  }
  // TODO remove macro definition assertions from problem?
  Trace("QME") << "definitions:\n\n" << d_macroDefinitions << endl << endl;
  // Apply macro substitutions:
  if (d_macroDefinitions.size() == 0)
  {
    return PreprocessingPassResult::NO_CONFLICT;
  }
  for (Node& assertion : assertions)
  {
    // TODO currently 10 quantifier regression tests fail when check-unsat-cores
    // is enabled
    Node current = replaceMacroInstances(assertion);
    if (current != assertion)
    {
      current = Rewriter::rewrite(current);
      Trace("QME") << "simplified rewritten node: " << current << endl;
      // Mark it as dependent on all assertions containing macro definitions;
      // this is an over-approximation.
      PROOF(ProofManager::currentPM()->addDependence(current, assertion);
            for (Node& macroAssertion
                 : macroAssertions) {
              if (macroAssertion != assertion)
              {
                ProofManager::currentPM()->addDependence(current,
                                                         macroAssertion);
              }
            });
      assertion = current;
    }
  }
  Trace("QME:all") << "rewritten assertions:" << endl;
  for (Node& assertion : assertions)
  {
    Trace("QME:all") << assertion << endl;
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
