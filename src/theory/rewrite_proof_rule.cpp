/*********************                                                        */
/*! \file rewrite_proof_rule.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of rewrite proof rule
 **/

#include "theory/rewrite_proof_rule.h"

#include "theory/rewrite_db_term_process.h"

#include "expr/node_algorithm.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

void RewritePfRule::init(const std::string& name,
                         const std::vector<Node>& cond,
                         Node eq)
{
  d_name = name;
  d_cond.clear();
  d_cond.insert(d_cond.end(), cond.begin(), cond.end());
  d_eq = eq;

  std::unordered_set<Node, NodeHashFunction> fvs;
  expr::getFreeVariables(eq, fvs);

  d_numFv = fvs.size();

  std::unordered_set<Node, NodeHashFunction> fvsCond;
  for (const Node& c : d_cond)
  {
    expr::getFreeVariables(c, fvsCond);
  }
  for (const Node& v : fvs)
  {
    d_fvs.push_back(v);
    if (fvsCond.find(v) == fvsCond.end())
    {
      d_noOccVars[v] = true;
    }
  }
}

}  // namespace theory
}  // namespace CVC4
