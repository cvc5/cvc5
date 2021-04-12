/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Tianyi Liang
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The extended theory callback for non-linear arithmetic
 */

#include "theory/arith/nl/ext_theory_callback.h"

#include "theory/arith/arith_utilities.h"
#include "theory/uf/equality_engine.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {

NlExtTheoryCallback::NlExtTheoryCallback(eq::EqualityEngine* ee) : d_ee(ee)
{
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
}

bool NlExtTheoryCallback::getCurrentSubstitution(
    int effort,
    const std::vector<Node>& vars,
    std::vector<Node>& subs,
    std::map<Node, std::vector<Node>>& exp)
{
  // get the constant equivalence classes
  std::map<Node, std::vector<int>> rep_to_subs_index;

  bool retVal = false;
  for (unsigned i = 0; i < vars.size(); i++)
  {
    Node n = vars[i];
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
        rep_to_subs_index[nr].push_back(i);
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

bool NlExtTheoryCallback::isExtfReduced(
    int effort, Node n, Node on, std::vector<Node>& exp, ExtReducedId& id)
{
  if (n != d_zero)
  {
    Kind k = n.getKind();
    if (k != NONLINEAR_MULT && !isTranscendentalKind(k) && k != IAND)
    {
      id = ExtReducedId::ARITH_SR_LINEAR;
      return true;
    }
    return false;
  }
  Assert(n == d_zero);
  id = ExtReducedId::ARITH_SR_ZERO;
  if (on.getKind() == NONLINEAR_MULT)
  {
    Trace("nl-ext-zero-exp")
        << "Infer zero : " << on << " == " << n << std::endl;
    // minimize explanation if a substitution+rewrite results in zero
    const std::set<Node> vars(on.begin(), on.end());

    for (unsigned i = 0, size = exp.size(); i < size; i++)
    {
      Trace("nl-ext-zero-exp")
          << "  exp[" << i << "] = " << exp[i] << std::endl;
      std::vector<Node> eqs;
      if (exp[i].getKind() == EQUAL)
      {
        eqs.push_back(exp[i]);
      }
      else if (exp[i].getKind() == AND)
      {
        for (const Node& ec : exp[i])
        {
          if (ec.getKind() == EQUAL)
          {
            eqs.push_back(ec);
          }
        }
      }

      for (unsigned j = 0; j < eqs.size(); j++)
      {
        for (unsigned r = 0; r < 2; r++)
        {
          if (eqs[j][r] == d_zero && vars.find(eqs[j][1 - r]) != vars.end())
          {
            Trace("nl-ext-zero-exp")
                << "...single exp : " << eqs[j] << std::endl;
            exp.clear();
            exp.push_back(eqs[j]);
            return true;
          }
        }
      }
    }
  }
  return true;
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5
