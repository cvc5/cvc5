/*********************                                                        */
/*! \file split_zero_check.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of split zero check
 **/

#include "theory/arith/nl/ext/split_zero_check.h"

#include "expr/node.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

SplitZeroCheck::SplitZeroCheck(ExtState* data, context::Context* ctx)
    : d_data(data), d_zero_split(ctx)
{
}

void SplitZeroCheck::check()
{
  for (unsigned i = 0; i < d_data->d_ms_vars.size(); i++)
  {
    Node v = d_data->d_ms_vars[i];
    if (d_zero_split.insert(v))
    {
      Node eq = v.eqNode(d_data->d_zero);
      eq = Rewriter::rewrite(eq);
      d_data->d_im.addPendingPhaseRequirement(eq, true);
      ArithLemma lem(eq.orNode(eq.negate()),
                     LemmaProperty::NONE,
                     nullptr,
                     InferenceId::NL_SPLIT_ZERO);
      d_data->d_im.addPendingArithLemma(lem);
    }
  }
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4