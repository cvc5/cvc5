/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * IDL extension.
 */

#include "theory/arith/idl/idl_extension.h"

#include <iomanip>
#include <queue>
#include <set>

#include "expr/node_builder.h"
#include "theory/arith/theory_arith.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace idl {

IdlExtension::IdlExtension(Env& env, TheoryArith& parent)
    : EnvObj(env),
      d_parent(parent),
      d_varMap(context()),
      d_varList(context()),
      d_facts(context()),
      d_numVars(0)
{
}

IdlExtension::~IdlExtension() {
}

void IdlExtension::preRegisterTerm(TNode node)
{
  Assert(d_numVars == 0);
  if (node.isVar())
  {
    Trace("theory::arith::idl")
        << "IdlExtension::preRegisterTerm(): processing var " << node
        << std::endl;
    unsigned size = d_varMap.size();
    d_varMap[node] = size;
    d_varList.push_back(node);
  }
}

void IdlExtension::presolve()
{
  d_numVars = d_varMap.size();
  Trace("theory::arith::idl")
      << "IdlExtension::preSolve(): d_numVars = " << d_numVars << std::endl;

  // Initialize adjacency matrix.
  for (size_t i = 0; i < d_numVars; ++i)
  {
    d_matrix.emplace_back(d_numVars);
    d_valid.emplace_back(d_numVars, false);
  }
}

void IdlExtension::notifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  Trace("theory::arith::idl")
      << "IdlExtension::notifyFact(): processing " << fact << std::endl;
  d_facts.push_back(fact);
}

Node IdlExtension::ppRewrite(TNode atom, std::vector<SkolemLemma>& lems)
{
  // We are only interested in predicates
  if (!atom.getType().isBoolean())
  {
    return atom;
  }

  Trace("theory::arith::idl")
      << "IdlExtension::ppRewrite(): processing " << atom << std::endl;
  NodeManager* nm = NodeManager::currentNM();

  if (atom[0].getKind() == Kind::CONST_RATIONAL)
  {
    // Move constant value to right-hand side
    Kind k = Kind::EQUAL;
    switch (atom.getKind())
    {
      // -------------------------------------------------------------------------
      // TODO: Handle these cases.
      // -------------------------------------------------------------------------
      case Kind::EQUAL:
      case Kind::LT:
      case Kind::LEQ:
      case Kind::GT:
      case Kind::GEQ:
      default: break;
    }
    return ppRewrite(nm->mkNode(k, atom[1], atom[0]), lems);
  }
  else if (atom[1].getKind() == Kind::VARIABLE)
  {
    // Handle the case where there are no constants, e.g., (= x y) where both
    // x and y are variables
    Node ret = atom;
    // -------------------------------------------------------------------------
    // TODO: Handle this case.
    // -------------------------------------------------------------------------
    return ret;
  }

  switch (atom.getKind())
  {
    case Kind::EQUAL:
    {
      Node l_le_r = nm->mkNode(Kind::LEQ, atom[0], atom[1]);
      Assert(atom[0].getKind() == Kind::SUB);
      Node negated_left = nm->mkNode(Kind::SUB, atom[0][1], atom[0][0]);
      const Rational& right = atom[1].getConst<Rational>();
      Node negated_right = nm->mkConstInt(-right);
      Node r_le_l = nm->mkNode(Kind::LEQ, negated_left, negated_right);
      return nm->mkNode(Kind::AND, l_le_r, r_le_l);
    }

    // -------------------------------------------------------------------------
    // TODO: Handle these cases.
    // -------------------------------------------------------------------------
    case Kind::LT:
    case Kind::LEQ:
    case Kind::GT:
    case Kind::GEQ:
      // -------------------------------------------------------------------------

    default: break;
  }
  return atom;
}

void IdlExtension::postCheck(Theory::Effort level)
{
  if (!Theory::fullEffort(level))
  {
    return;
  }

  Trace("theory::arith::idl")
      << "IdlExtension::postCheck(): number of facts = " << d_facts.size()
      << std::endl;

  // Reset the graph
  for (size_t i = 0; i < d_numVars; i++)
  {
    for (size_t j = 0; j < d_numVars; j++)
    {
      d_valid[i][j] = false;
    }
  }

  for (Node fact : d_facts)
  {
    // For simplicity, we reprocess all the literals that have been asserted to
    // this theory solver. A better implementation would process facts in
    // notifyFact().
    Trace("theory::arith::idl")
        << "IdlExtension::check(): processing " << fact << std::endl;
    processAssertion(fact);
  }

  if (negativeCycle())
  {
    // Return a conflict that includes all the literals that have been asserted
    // to this theory solver. A better implementation would only include the
    // literals involved in the conflict here.
    NodeBuilder conjunction(Kind::AND);
    for (Node fact : d_facts)
    {
      conjunction << fact;
    }
    Node conflict = conjunction;
    // Send the conflict using the inference manager. Each conflict is assigned
    // an ID. Here, we use  ARITH_CONF_IDL_EXT, which indicates a generic
    // conflict detected by this extension
    d_parent.getInferenceManager().conflict(conflict,
                                            InferenceId::ARITH_CONF_IDL_EXT);
    return;
  }
}

bool IdlExtension::collectModelInfo(TheoryModel* m,
                                    const std::set<Node>& termSet)
{
  std::vector<Rational> distance(d_numVars, Rational(0));

  // ---------------------------------------------------------------------------
  // TODO: implement model generation by computing the single-source shortest
  // path from a node that has distance zero to all other nodes
  // ---------------------------------------------------------------------------

  NodeManager* nm = NodeManager::currentNM();
  for (size_t i = 0; i < d_numVars; i++)
  {
    // Assert that the variable's value is equal to its distance in the model
    m->assertEquality(d_varList[i], nm->mkConstInt(distance[i]), true);
  }

  return true;
}

void IdlExtension::processAssertion(TNode assertion)
{
  bool polarity = assertion.getKind() != Kind::NOT;
  TNode atom = polarity ? assertion : assertion[0];
  Assert(atom.getKind() == Kind::LEQ);
  Assert(atom[0].getKind() == Kind::SUB);
  TNode var1 = atom[0][0];
  TNode var2 = atom[0][1];

  Rational value = (atom[1].getKind() == Kind::NEG)
                       ? -atom[1][0].getConst<Rational>()
                       : atom[1].getConst<Rational>();

  if (!polarity)
  {
    std::swap(var1, var2);
    value = -value - Rational(1);
  }

  size_t index1 = d_varMap[var1];
  size_t index2 = d_varMap[var2];

  if (!d_valid[index1][index2] || value < d_matrix[index1][index2])
  {
    d_valid[index1][index2] = true;
    d_matrix[index1][index2] = value;
  }
}

bool IdlExtension::negativeCycle()
{
  // --------------------------------------------------------------------------
  // TODO: write the code to detect a negative cycle.
  // --------------------------------------------------------------------------

  return false;
}

void IdlExtension::printMatrix(const std::vector<std::vector<Rational>>& matrix,
                               const std::vector<std::vector<bool>>& valid)
{
  std::cout << "      ";
  for (size_t j = 0; j < d_numVars; ++j)
  {
    std::cout << std::setw(6) << d_varList[j];
  }
  std::cout << std::endl;
  for (size_t i = 0; i < d_numVars; ++i)
  {
    std::cout << std::setw(6) << d_varList[i];
    for (size_t j = 0; j < d_numVars; ++j)
    {
      if (valid[i][j])
      {
        std::cout << std::setw(6) << matrix[i][j];
      }
      else
      {
        std::cout << std::setw(6) << "oo";
      }
    }
    std::cout << std::endl;
  }
}

}  // namespace idl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5
