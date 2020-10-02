/*********************                                                        */
/*! \file arith_preprocess.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Arithmetic preprocess
 **/

#include "theory/arith/arith_preprocess.h"

namespace CVC4 {
namespace theory {
namespace arith {

ArithPreprocess::ArithPreprocess(ArithState& state, InferenceManager& im, ProofNodeManager* pnm, const LogicInfo& info) : d_im(im), d_opElim(pnm, info), d_reduced(state.getUserContext()){}
bool ArithPreprocess::reduceAssertion(TNode atom)
{
  return false;
}
bool ArithPreprocess::isReduced(TNode atom) const
{
  return false;
}

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

