/*********************                                                        */
/*! \file term_registry.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of bags term registry object
 **/

#include "theory/bags/term_registry.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace bags {

TermRegistry::TermRegistry(SolverState& state,
                           InferenceManager& im)
    : d_im(im),
      d_proxy(state.getUserContext()),
      d_proxy_to_term(state.getUserContext())
{
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4
