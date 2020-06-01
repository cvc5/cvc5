/*********************                                                        */
/*! \file nl_constraint.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of utilities for non-linear constraints
 **/

#include "theory/arith/nl/nl_constraint.h"

#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

ConstraintDb::ConstraintDb(MonomialDb& mdb) : d_mdb(mdb) {}

void ConstraintDb::registerConstraint(Node atom)
{
  if (std::find(d_constraints.begin(), d_constraints.end(), atom)
      != d_constraints.end())
  {
    return;
  }
  d_constraints.push_back(atom);
  Trace("nl-ext-debug") << "Register constraint : " << atom << std::endl;
  std::map<Node, Node> msum;
  if (ArithMSum::getMonomialSumLit(atom, msum))
  {
    Trace("nl-ext-debug") << "got monomial sum: " << std::endl;
    if (Trace.isOn("nl-ext-debug"))
    {
      ArithMSum::debugPrintMonomialSum(msum, "nl-ext-debug");
    }
    unsigned max_degree = 0;
    std::vector<Node> all_m;
    std::vector<Node> max_deg_m;
    for (std::map<Node, Node>::iterator itm = msum.begin(); itm != msum.end();
         ++itm)
    {
      if (!itm->first.isNull())
      {
        all_m.push_back(itm->first);
        d_mdb.registerMonomial(itm->first);
        Trace("nl-ext-debug2")
            << "...process monomial " << itm->first << std::endl;
        unsigned d = d_mdb.getDegree(itm->first);
        if (d > max_degree)
        {
          max_degree = d;
          max_deg_m.clear();
        }
        if (d >= max_degree)
        {
          max_deg_m.push_back(itm->first);
        }
      }
    }
    // isolate for each maximal degree monomial
    for (unsigned i = 0; i < all_m.size(); i++)
    {
      Node m = all_m[i];
      Node rhs, coeff;
      int res = ArithMSum::isolate(m, msum, coeff, rhs, atom.getKind());
      if (res != 0)
      {
        Kind type = atom.getKind();
        if (res == -1)
        {
          type = reverseRelationKind(type);
        }
        Trace("nl-ext-constraint") << "Constraint : " << atom << " <=> ";
        if (!coeff.isNull())
        {
          Trace("nl-ext-constraint") << coeff << " * ";
        }
        Trace("nl-ext-constraint")
            << m << " " << type << " " << rhs << std::endl;
        ConstraintInfo& ci = d_c_info[atom][m];
        ci.d_rhs = rhs;
        ci.d_coeff = coeff;
        ci.d_type = type;
      }
    }
    for (unsigned i = 0; i < max_deg_m.size(); i++)
    {
      Node m = max_deg_m[i];
      d_c_info_maxm[atom][m] = true;
    }
  }
  else
  {
    Trace("nl-ext-debug") << "...failed to get monomial sum." << std::endl;
  }
}

const std::map<Node, std::map<Node, ConstraintInfo> >&
ConstraintDb::getConstraints()
{
  return d_c_info;
}

bool ConstraintDb::isMaximal(Node atom, Node x) const
{
  std::map<Node, std::map<Node, bool> >::const_iterator itcm =
      d_c_info_maxm.find(atom);
  Assert(itcm != d_c_info_maxm.end());
  return itcm->second.find(x) != itcm->second.end();
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
