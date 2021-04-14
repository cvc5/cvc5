/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of bags term registry object.
 */

#include "theory/bags/term_registry.h"

#include "theory/bags/inference_manager.h"
#include "theory/bags/solver_state.h"

using namespace std;
using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace bags {

TermRegistry::TermRegistry(SolverState& state, InferenceManager& im)
    : d_im(im),
      d_proxy(state.getUserContext()),
      d_proxy_to_term(state.getUserContext())
{
}

Node TermRegistry::getEmptyBag(TypeNode tn)
{
  std::map<TypeNode, Node>::iterator it = d_emptybag.find(tn);
  if (it != d_emptybag.end())
  {
    return it->second;
  }
  Node n = NodeManager::currentNM()->mkConst(EmptySet(tn));
  d_emptybag[tn] = n;
  return n;
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5
