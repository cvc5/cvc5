/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of bags term registry object.
 */

#include "theory/bags/term_registry.h"

#include "expr/emptyset.h"
#include "theory/bags/inference_manager.h"
#include "theory/bags/solver_state.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace bags {

TermRegistry::TermRegistry(Env& env, SolverState& state, InferenceManager& im)
    : EnvObj(env),
      d_im(im),
      d_proxy(userContext()),
      d_proxy_to_term(userContext())
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
}  // namespace cvc5::internal
