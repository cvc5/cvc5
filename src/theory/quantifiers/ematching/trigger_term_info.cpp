/*********************                                                        */
/*! \file trigger_term_info.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of trigger term info class
 **/

#include "theory/quantifiers/ematching/trigger_term_info.h"

#include "theory/quantifiers/ematching/pattern_term_selector.h"
#include "theory/quantifiers/term_util.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace inst {

void TriggerTermInfo::init(Node q, Node n, int reqPol, Node reqPolEq)
{
  if (d_fv.empty())
  {
    quantifiers::TermUtil::computeInstConstContainsForQuant(q, n, d_fv);
  }
  if (d_reqPol == 0)
  {
    d_reqPol = reqPol;
    d_reqPolEq = reqPolEq;
  }
  else
  {
    // determined a ground (dis)equality must hold or else q is a tautology?
  }
  d_weight = PatternTermSelector::getTriggerWeight(n);
}


}  // namespace inst
}  // namespace theory
}  // namespace CVC4
