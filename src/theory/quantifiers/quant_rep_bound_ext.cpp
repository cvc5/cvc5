/*********************                                                        */
/*! \file quant_rep_bound_ext.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of quantifiers representative bound utility
 **/

#include "theory/quantifiers/quant_rep_bound_ext.h"

#include "theory/quantifiers_engine.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

QRepBoundExt::QRepBoundExt(QuantifiersEngine * qe)
: d_qe(qe)
{
}
  
RsiEnumType QRepBoundExt::setBound(Node owner,
                                                   unsigned i,
                                                   std::vector<Node>& elements)
{
  // builtin: check if it is bound by bounded integer module
  if (owner.getKind() == FORALL)
  {
    if (d_qe->isBoundVar(owner, owner[0][i]))
    {
      unsigned bvt =
          d_qe->getBoundVarType(owner, owner[0][i]);
      if (bvt != BoundedIntegers::BOUND_FINITE)
      {
        d_bound_int[i] = true;
        return ENUM_CUSTOM;
      }
      else
      {
        // indicates the variable is finitely bound due to
        // the (small) cardinality of its type,
        // will treat in default way
      }
    }
  }
  return ENUM_INVALID;
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
    if (!d_qe->getBoundElements(
            rsi, initial, owner, owner[0][i], elements))
    {
      return false;
    }
  }
  return true;
}

bool QRepBoundExt::initializeRepresentativesForType(TypeNode tn)
{
  return d_qe->getModel()->initializeRepresentativesForType(tn);
}

bool QRepBoundExt::getVariableOrder(Node owner, std::vector<unsigned>& varOrder)
{
  // must set a variable index order based on bounded integers
  if (owner.getKind() != FORALL)
  {
    return false;
  }
  Trace("bound-int-rsi") << "Calculating variable order..." << std::endl;
  // we take the bounded variables first
  for (unsigned i = 0, nbvs = d_qe->getNumBoundVars(owner); i < nbvs;
        i++)
  {
    Node v = d_qe->getBoundVar(owner, i);
    Trace("bound-int-rsi") << "  bound var #" << i << " is " << v
                            << std::endl;
    varOrder.push_back(d_qe->getTermUtil()->getVariableNum(owner, v));
  }
  // then the unbounded ones
  for (const Node& v : owner[0])
  {
    if (!d_qe->isBoundVar(owner, v))
    {
      varOrder.push_back(i);
    }
  }
  return true;
}


} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
