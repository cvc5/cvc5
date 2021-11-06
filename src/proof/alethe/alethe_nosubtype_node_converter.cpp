/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Alethe node conversion to remove subtyping
 */

#include "proof/alethe/alethe_nosubtype_node_converter.h"

#include "theory/theory.h"

namespace cvc5 {
namespace proof {

Node AletheNoSubtypeNodeConverter::postConvert(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  // corce function applications
  if (n.getKind() == kind::APPLY_UF)
  {
    Node op = n.getOperator();
    TypeNode tn = op.getType();
    std::vector<TypeNode> argTypes = tn.getArgTypes();
    // if any of the argument types is real, in case the argument of that
    // position is an integer constant we must turn it into a real constant
    // look at all args, if any is an integer constant, transform it
    bool childChanged = false;
    std::vector<Node> children{op};
    for (size_t i = 0, size = n.getNumChildren(); i < size; ++i)
    {
      if (!argTypes[i].isReal() || argTypes[i].isInteger()
          || !n[i].getType().isInteger())
      {
        children.push_back(n[i]);
        continue;
      }
      Trace("alethe-proof-subtyping")
          << "\t\t..fun app arg " << i << " is integer term " << n[i]
          << " in real position.\n";
      if (!n[i].isConst())
      {
        Unreachable() << "AletheBackend: Can't handle subtyping case of "
                         "non-value integers.\n";
      }
      childChanged = true;
      children.push_back(nm->mkNode(kind::CAST_TO_REAL, n[i]));
    }
    if (childChanged)
    {
      return nm->mkNode(kind::APPLY_UF, children);
    }
    return n;
  }
  // Ignore interpreted terms that are not applications of arithmetic operators
  // (or equalities between arithmetic terms) which may have a real and an
  // integer argument
  if (n.getNumChildren() < 2
      || theory::Theory::theoryOf(n) != theory::TheoryId::THEORY_ARITH)
  {
    if (n.getNumChildren() > 1)
    {
      Trace("alethe-proof-subtyping2") << "\tIgnoring " << n << " with theory "
                                       << theory::Theory::theoryOf(n) << "\n";
    }
    return n;
  }
  Trace("alethe-proof-subtyping2")
      << "\tCheck " << n << " of kind " << n.getKind() << "\n";
  // coerce equalities where one of the terms is real and the other integer.
  // This handles for example the case instantiation
  bool childChanged = false;
  std::vector<Node> children{n.begin(), n.end()};
  bool hasReal = false;
  size_t i, size = n.getNumChildren();
  for (i = 0; i < size; ++i)
  {
    if (n[i].getType().isReal())
    {
      hasReal = true;
      break;
    }
  }
  if (hasReal)
  {
    for (i = 0; i < size; ++i)
    {
      if (n[i].getType().isInteger())
      {
        Trace("alethe-proof-subtyping") << "\t\t..arith term arg " << n[i]
                                        << " is integer but should be real\n";
        if (!n[i].isConst())
        {
          Unreachable() << "AletheBackend: Can't handle subtyping case of "
                           "non-value integers.\n";
        }
        childChanged = true;
        children[i] = nm->mkNode(kind::CAST_TO_REAL, n[i]);
        break;
      }
    }
    if (childChanged)
    {
      return nm->mkNode(n.getKind(), children);
    }
  }
  return n;
}

}  // namespace proof
}  // namespace cvc5
