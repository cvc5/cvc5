/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The extended theory callback for liastar arithmetic.
 */

#include "theory/arith/liastar/liastar_ext_theory_callback.h"

#include "theory/arith/arith_utilities.h"
#include "theory/uf/equality_engine.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

LiaStarExtTheoryCallback::LiaStarExtTheoryCallback(eq::EqualityEngine* ee)
    : d_ee(ee)
{
}

bool LiaStarExtTheoryCallback::getCurrentSubstitution(
    int effort,
    const std::vector<Node>& vars,
    std::vector<Node>& subs,
    std::map<Node, std::vector<Node>>& exp)
{
  // get the constant equivalence classes
  bool retVal = false;
  for (const Node& n : vars)
  {
    if (d_ee->hasTerm(n))
    {
      Node nr = d_ee->getRepresentative(n);
      if (nr.isConst())
      {
        subs.push_back(nr);
        Trace("nl-subs") << "Basic substitution : " << n << " -> " << nr
                         << std::endl;
        exp[n].push_back(n.eqNode(nr));
        retVal = true;
      }
      else
      {
        subs.push_back(n);
      }
    }
    else
    {
      subs.push_back(n);
    }
  }
  // return true if the substitution is non-trivial
  return retVal;
}

bool LiaStarExtTheoryCallback::isExtfReduced(
    int effort, Node n, Node on, std::vector<Node>& exp, ExtReducedId& id)
{
  return n.isConst();
}

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
