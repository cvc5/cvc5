/*********************                                                        */
/*! \file quant_rep_bound_ext.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of quantifiers representative bound utility
 **/

#include "theory/quantifiers/quant_rep_bound_ext.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory::quantifiers::fmcheck;

namespace CVC4 {
namespace theory {
namespace quantifiers {

QRepBoundExt::QRepBoundExt(QuantifiersEngine * qe)
: d_qe(qe)
{
}
  
RepSetIterator::RsiEnumType QRepBoundExt::setBound(Node owner,
                                                   unsigned i,
                                                   std::vector<Node>& elements)
{
  // builtin: check if it is bound by bounded integer module
  if (owner.getKind() == FORALL && d_bi)
  {
    if (d_bi->isBoundVar(owner, owner[0][i]))
    {
      unsigned bvt =
          d_bi->getBoundVarType(owner, owner[0][i]);
      if (bvt != BoundedIntegers::BOUND_FINITE)
      {
        d_bound_int[i] = true;
        return RepSetIterator::ENUM_BOUND_INT;
      }
      else
      {
        // indicates the variable is finitely bound due to
        // the (small) cardinality of its type,
        // will treat in default way
      }
    }
  }
  return RepSetIterator::ENUM_INVALID;
}

bool QRepBoundExt::resetIndex(RepSetIterator* rsi,
                              Node owner,
                              unsigned i,
                              bool initial,
                              std::vector<Node>& elements)
{
  if (d_bound_int.find(i) != d_bound_int.end())
  {
    Assert(owner.getKind() == FORALL);
    Assert(d_bi != nullptr);
    if (!d_bi->getBoundElements(
            rsi, initial, owner, owner[0][i], elements))
    {
      return false;
    }
  }
  return true;
}

bool QRepBoundExt::initializeRepresentativesForType(TypeNode tn)
{
  return d_model->initializeRepresentativesForType(tn);
}

bool QRepBoundExt::getVariableOrder(Node owner, std::vector<unsigned>& varOrder)
{
  // must set a variable index order based on bounded integers
  if (owner.getKind() != FORALL || !d_bi)
  {
    return false;
  }
  Trace("bound-int-rsi") << "Calculating variable order..." << std::endl;
  for (unsigned i = 0, nbvs = d_bi->getNumBoundVars(owner); i < nbvs;
        i++)
  {
    Node v = d_bi->getBoundVar(owner, i);
    Trace("bound-int-rsi") << "  bound var #" << i << " is " << v
                            << std::endl;
    varOrder.push_back(d_qe->getTermUtil()->getVariableNum(owner, v));
  }
  for (unsigned i = 0; i < owner[0].getNumChildren(); i++)
  {
    if (!d_bi->isBoundVar(owner, owner[0][i]))
    {
      varOrder.push_back(i);
    }
  }
  return true;
}


} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
