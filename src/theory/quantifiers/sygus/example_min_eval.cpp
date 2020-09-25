/*********************                                                        */
/*! \file example_min_eval.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of utility for minimizing the number of calls to
 ** evaluate a term on substitutions with a fixed domain.
 **/

#include "theory/quantifiers/sygus/example_min_eval.h"

#include "expr/node_algorithm.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

ExampleMinEval::ExampleMinEval(Node n,
                               const std::vector<Node>& vars,
                               EmeEval* ece)
{
  AlwaysAssert(d_evalNode.isNull());
  d_evalNode = n;
  d_vars.insert(d_vars.end(), vars.begin(), vars.end());

  // compute its free variables
  std::unordered_set<Node, NodeHashFunction> fvs;
  expr::getFreeVariables(n, fvs);
  for (size_t i = 0, vsize = vars.size(); i < vsize; i++)
  {
    if (fvs.find(vars[i]) != fvs.end())
    {
      // will use this index
      d_indices.push_back(i);
    }
  }
  Trace("example-cache") << "For " << n << ", " << d_indices.size() << " / "
                         << d_vars.size() << " variables are relevant"
                         << std::endl;
  d_ece = ece;
}

Node ExampleMinEval::evaluate(const std::vector<Node>& subs)
{
  Assert(d_vars.size() == subs.size());

  if (d_indices.size() == d_vars.size())
  {
    // no sharing is possible since all variables are relevant, just evaluate
    return d_ece->eval(d_evalNode, d_vars, subs);
  }

  // get the subsequence of subs that is relevant
  std::vector<Node> relSubs;
  for (unsigned i = 0, ssize = d_indices.size(); i < ssize; i++)
  {
    relSubs.push_back(subs[d_indices[i]]);
  }
  Node res = d_trie.existsTerm(relSubs);
  if (res.isNull())
  {
    // not already cached, must evaluate
    res = d_ece->eval(d_evalNode, d_vars, subs);

    // add to trie
    d_trie.addTerm(res, relSubs);
  }
  return res;
}

Node EmeEvalTds::eval(TNode n,
                      const std::vector<Node>& args,
                      const std::vector<Node>& vals)
{
  return d_tds->evaluateBuiltin(d_tn, n, vals);
}

}  // namespace quantifiers
}  // namespace theory
} /* namespace CVC4 */
