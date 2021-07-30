/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sequences solver for seq.nth/seq.update.
 */

#include "theory/strings/sequences_array_solver.h"

#include "util/rational.h"
#include "theory/strings/theory_strings_utils.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace strings {

SequencesArraySolver::SequencesArraySolver(SolverState& s,
                                             InferenceManager& im,
                                             TermRegistry& tr,
                                             ExtfSolver& es)
    : d_state(s), d_im(im), d_termReg(tr), d_esolver(es)
{
}

SequencesArraySolver::~SequencesArraySolver() {}

void SequencesArraySolver::check(const std::vector<Node>& nthTerms,
             const std::vector<Node>& updateTerms)
{
  NodeManager * nm = NodeManager::currentNM();

  std::map<Node, std::vector<Node>> index_map;

  Trace("seq-update") << "SequencesArraySolver::check..." << std::endl;
  d_writeModel.clear();
  for (const Node& n : nthTerms)
  {
    // (seq.nth n[0] n[1])
    Node r = d_state.getRepresentative(n[0]);
    Trace("seq-update") << "- " << r << ": " << n[1] << " -> " << n << std::endl;
    //    d_writeModel[r][n[1]] = n;
    if (index_map.find(r) == index_map.end())
    {
      std::vector<Node> indexes;
      indexes.push_back(n[1]);
      index_map[r] = indexes;
    }
    else
    {
      index_map[r].push_back(n[1]);
    }
  }
  for (const Node& n : updateTerms)
  {
    // (seq.update x i (seq.unit z))
    // possible lemma: (seq.nth (seq.update x, i, (seq.unit z)) i) == z
    // note the left side could rewrites to z
    // get proxy variable for the update term as t
    // d_termReg.getProxyVariable
    // send lemma: (seq.nth t i) == z
    Node proxyVar = d_termReg.getProxyVariableFor(n);
    Trace("seq-update") << "- " << proxyVar << " = " << n << std::endl;

    // t == (seq.update x i (seq.unit z))
    // => (seq.nth t i) == z
    std::vector<Node> exp;
    d_im.addToExplanation(proxyVar, n, exp);
    Node left = nm->mkNode(SEQ_NTH, proxyVar, n[1]);
    Node right = nm->mkNode(SEQ_NTH, n[2], nm->mkConst(Rational(0)));
    right = Rewriter::rewrite(right);

    if (!d_state.areEqual(left, right))
    {
      Node eq = nm->mkNode(EQUAL, left, right);
      InferenceId iid = InferenceId::STRINGS_SU_UPDATE_UNIT;
      std::cerr << "send by check() in sequence_array " << left << " " << right
                << std::endl;
      d_im.sendInference(exp, eq, iid);
    }

    // i != j => (seq.nth (seq.update a i x) j) == (seq.nth a j)
    // std::vector<Node> exp;
    // d_im.addToExplanation(proxyVar, n, exp);
    for (auto nth : index_map)
    {
      Node seq = nth.first;
      if (d_state.areEqual(seq, n))
      {
        std::vector<Node> indexes = nth.second;
        for (Node j : indexes)
        {
          Node left = nm->mkNode(DISTINCT, n[1], j);
          Node nth1 = nm->mkNode(SEQ_NTH, proxyVar, j);
          Node nth2 = nm->mkNode(SEQ_NTH, n[0], j);
          Node right = nm->mkNode(EQUAL, nth1, nth2);
          Node lem = nm->mkNode(IMPLIES, left, right);
          if (!d_state.areEqual(nth1, nth2))
          {
            InferenceId iid = InferenceId::STRINGS_SU_UPDATE_UNIT;
            std::cerr << "send by check() in sequence_array " << left << " -> "
                      << right << std::endl;
            d_im.sendInference(exp, lem, iid);
          }
        }
      }
    }
  }
}

const std::map<Node, Node>& SequencesArraySolver::getWriteModel(Node eqc)
{
  return d_writeModel[eqc];
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5
