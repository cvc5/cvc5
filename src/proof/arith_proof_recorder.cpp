/*********************                                                        */
/*! \file arith_proof_recorder.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A class for recording the skeletons of arithmetic proofs at solve
 ** time so they can later be used during proof-production time.
 **/

#include "proof/arith_proof_recorder.h"

#include <algorithm>
#include <vector>

#include "base/map_util.h"

namespace CVC4 {
namespace proof {

ArithProofRecorder::ArithProofRecorder() : d_lemmasToFarkasCoefficients()
{
  // Nothing else
}
void ArithProofRecorder::saveFarkasCoefficients(
    Node conflict, theory::arith::RationalVectorCP farkasCoefficients)
{
  // Verify that the conflict is a conjuction of (possibly negated) real bounds
  // Verify that the conflict is a conjunciton ...
  Assert(conflict.getKind() == kind::AND);
  Assert(conflict.getNumChildren() == farkasCoefficients->size());
  for (size_t i = 0, nchildren = conflict.getNumChildren(); i < nchildren; ++i)
  {
    const Node& child = conflict[i];
    // ... of possibly negated ...
    const Node& nonNegativeChild =
        child.getKind() == kind::NOT ? child[0] : child;
    // ... real bounds
    Assert(nonNegativeChild.getType().isBoolean()
           && nonNegativeChild[0].getType().isReal());
  }
  Debug("pf::arith") << "Saved Farkas Coefficients:" << std::endl;
  if (Debug.isOn("pf::arith"))
  {
    for (size_t i = 0, nchildren = conflict.getNumChildren(); i < nchildren;
         ++i)
    {
      const Node& child = conflict[i];
      const Rational& r = (*farkasCoefficients)[i];
      Debug("pf::arith") << "  " << std::setw(8) << r;
      Debug("pf::arith") << "  " << child << std::endl;
    }
  }

  std::set<Node> lits;
  std::copy(
      conflict.begin(), conflict.end(), std::inserter(lits, lits.begin()));

  d_lemmasToFarkasCoefficients[lits] =
      std::make_pair(std::move(conflict), *farkasCoefficients);
}

bool ArithProofRecorder::hasFarkasCoefficients(
    const std::set<Node>& conflict) const
{
  return d_lemmasToFarkasCoefficients.find(conflict)
         != d_lemmasToFarkasCoefficients.end();
}

std::pair<Node, theory::arith::RationalVectorCP>
ArithProofRecorder::getFarkasCoefficients(const std::set<Node>& conflict) const
{
  if (auto *p = FindOrNull(d_lemmasToFarkasCoefficients, conflict))
  {
    return std::make_pair(p->first, &p->second);
  }
  else
  {
    return std::make_pair(Node(), theory::arith::RationalVectorCPSentinel);
  }
}

}  // namespace proof
}  // namespace CVC4
