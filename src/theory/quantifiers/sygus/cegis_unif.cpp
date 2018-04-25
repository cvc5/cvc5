/*********************                                                        */
/*! \file cegis_unif.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief implementation of class for cegis with unification techniques
 **/

#include "theory/quantifiers/sygus/cegis_unif.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

CegisUnif::CegisUnif(QuantifiersEngine* qe, CegConjecture* p)
    : SygusModule(qe, p)
{
  d_tds = d_qe->getTermDatabaseSygus();
}

CegisUnif::~CegisUnif() {

}
void CegConjecturePbe::collectConstraints(Node n,
                                          std::map<Node, bool>& visited,
                                          bool hasPol,
                                          bool pol)
{
  if (visited.find(n) != visited.end())
  {
    return;
  }
  visited[n] = true;
  Node neval, n_output;
  /* Atomic predicate */
  if (n.getKind() == APPLY_UF && n.getNumChildren() > 0)
  {
    neval = n;
    if (hasPol)
    {
      n_output = !pol ? d_true : d_false;
    }
  }
  /* Equality between a function application and a constant */
  else if (n.getKind() == EQUAL && hasPol && !pol)
  {
    for (unsigned i = 0; i < 2; ++i)
    {
      if (n[i].getKind() == APPLY_UF && n[i].getNumChildren() > 0)
      {
        neval = n[i];
        if (n[1 - i].isConst())
        {
          n_output = n[1 - i];
        }
      }
    }
  }
  Assert(neval.isNull()
         || (neval.getKind() == APPLY_UF && neval.getNumChildren() > 0));
  /* Whether function to synthesize */
  if (!neval.isNull() && d_constraints.find(neval[0]) != d_constraints.end())
  {
    std::map<Node, bool>::iterator itx = d_examples_invalid.find(neval[0]);
    if (itx == d_examples_invalid.end())
    {
      /* collect point */
      std::vector<Node> pt;
      unsigned i, size;
      for (i = 1, size = neval.getNumChildren(); i < size; ++i)
      {
        if (!neval[i].isConst())
        {
          break;
        }
        pt.push_back(neval[i]);
      }
      if (i == size)
      {
        d_examples[neval[0]].push_back(pt);
        d_examples_out[neval[0]].push_back(n_output);
        d_examples_term[neval[0]].push_back(neval);
        Assert(!n_output.isNull() || n_output.isConst());
        if (n_output.isNull())
        {
          d_examples_out_invalid[neval[0]] = true;
        }
        /* finished processing this node */
        return;
      }
      /* HB why is this not a return also? */
      d_examples_invalid[neval[0]] = true;
      d_examples_out_invalid[neval[0]] = true;
    }
  }
  /* Recurse down */
  for (unsigned i = 0, size = n.getNumChildren(); i < size; ++i)
  {
    bool newPol, newHasPol;
    QuantPhaseReq::getPolarity(n, i, hasPol, pol, newHasPol, newPol);
    collectConstraints(n[i], visited, newHasPol, newPol);
  }
}

bool CegisUnif::initialize(Node n,
                           const std::vector<Node>& candidates,
                           std::vector<Node>& lemmas)
{
  Trace("sygus-ice") << "Initialize CegisUnif : " << n << std::endl;

  for (unsigned i = 0, size = candidates.size(); i < size; ++i)
  {
    Node f = candidates[i];
    d_constraints[f].clear();
  }
  std::map<Node, bool> visited;
  collectConstraints(n, visited, true, true);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
