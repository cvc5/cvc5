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
                                           CoreSolver& cs,
                                           ExtfSolver& es,
                                           ExtTheory& extt)
    : d_state(s),
      d_im(im),
      d_termReg(tr),
      d_csolver(cs),
      d_esolver(es),
      d_extt(extt),
      d_lem(s.getSatContext())
{
}

SequencesArraySolver::~SequencesArraySolver() {}

void SequencesArraySolver::checkUpdate(const std::vector<Node>& updateTerms)
{
  NodeManager * nm = NodeManager::currentNM();

  for (const Node& n : updateTerms)
  {
    // TODO: if n[2].kind == SEQ_UNIT

    // (seq.update x i (seq.unit z))
    // possible lemma: (seq.nth (seq.update x, i, (seq.unit z)) i) == z
    // note the left side could rewrites to z
    // get proxy variable for the update term as t
    // d_termReg.getProxyVariable
    // send lemma: (seq.nth t i) == z
    Node termProxy = d_termReg.getProxyVariableFor(n);
    Trace("seq-update") << "- " << termProxy << " = " << n << std::endl;

    // t == (seq.update x i (seq.unit z)) ^ i\in range(x)
    // => (seq.nth t i) == z
    std::vector<Node> exp;
    d_im.addToExplanation(termProxy, n, exp);
    //	Node lb = (nm->mkNode(LEQ, nm->mkConst(Rational(0)), n[1])); // 0 <= i
    //	Node ub = (nm->mkNode(LT, n[1], nm->mkNode(STRING_LENGTH, n[0]))); // i
    //< len(termProxy) 	Node range = nm->mkNode(AND, lb, ub); 	std::cerr << range
    //<< std::endl; 	exp.push_back(range); // 0 <= i ^ i < len(t)
    Node left = nm->mkNode(SEQ_NTH, termProxy, n[1]);
    Node right =
        nm->mkNode(SEQ_NTH, n[2], nm->mkConst(Rational(0)));  // n[2][0]
    right = Rewriter::rewrite(right);

    if (!d_state.areEqual(left, right))
    {
      Node eq = nm->mkNode(EQUAL, left, right);
      InferenceId iid = InferenceId::STRINGS_SU_UPDATE_UNIT;
      Trace("seq-update") << "send lemma - " << eq << std::endl;
      d_im.sendInference(exp, eq, iid);
    }

    // i != j ^ i, j \in range(a)
	// => (seq.nth (seq.update a i x) j) == (seq.nth a j)
    for (auto nth : d_index_map)
    {
      Node seq = nth.first;
      if (d_state.areEqual(seq, n) || d_state.areEqual(seq, n[0]))
      {
        std::set<Node> indexes = nth.second;
        for (Node j : indexes)
        {
          left = nm->mkNode(DISTINCT, n[1], j);
          Node nth1 = nm->mkNode(SEQ_NTH, termProxy, j);
          Node nth2 = nm->mkNode(SEQ_NTH, n[0], j);
          right = nm->mkNode(EQUAL, nth1, nth2);
		  // exp.push_back(left)
          Node lem = nm->mkNode(IMPLIES, left, right);
          if (d_lem.find(lem) == d_lem.end())
          {
            d_lem.insert(lem);
            InferenceId iid = InferenceId::STRINGS_SU_UPDATE_UNIT;
            Trace("seq-update") << "send lemma - " << lem << std::endl;
			// d_im.sendInference(exp, right, iid);
            d_im.sendInference(exp, lem, iid);
          }
        }
      }
    }
  }
}

void SequencesArraySolver::check(const std::vector<Node>& nthTerms,
                                 const std::vector<Node>& updateTerms)
{
  NodeManager* nm = NodeManager::currentNM();

  Trace("seq-update") << "SequencesArraySolver::check..." << std::endl;
  d_writeModel.clear();
  for (const Node& n : nthTerms)
  {
    // (seq.nth n[0] n[1])
    Node r = d_state.getRepresentative(n[0]);
    // Trace("seq-update") << "- " << r << ": " << n[1] << " -> " << n <<
    // std::endl;
    //    d_writeModel[r][n[1]] = n;
    if (d_index_map.find(r) == d_index_map.end())
    {
      std::set<Node> indexes;
      indexes.insert(n[1]);
      d_index_map[r] = indexes;
    }
    else
    {
      d_index_map[r].insert(n[1]);
    }

    if (n[0].getKind() == STRING_REV)
    {
      Node s = n[0][0];
      Node i = n[1];
      Node sLen = nm->mkNode(STRING_LENGTH, s);
      Node iRev = nm->mkNode(
          MINUS, sLen, nm->mkNode(PLUS, i, nm->mkConst(Rational(1))));

      std::vector<Node> nexp;
      nexp.push_back(nm->mkNode(LEQ, nm->mkConst(Rational(0)), i));
      nexp.push_back(nm->mkNode(LT, i, sLen));

      // 0 <= i ^ i < len(s) => seq.nth(seq.rev(s), i) = seq.nth(s, len(s) - i -
      // 1)
      Node ret = nm->mkNode(SEQ_NTH, s, iRev);
      d_im.sendInference(
          {}, nexp, n.eqNode(ret), InferenceId::STRINGS_SU_NTH_REV);
      d_extt.markReduced(n, ExtReducedId::STRINGS_NTH_REV);
    }
  }
  checkUpdate(updateTerms);
}

const std::map<Node, Node>& SequencesArraySolver::getWriteModel(Node eqc)
{
  return d_writeModel[eqc];
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5
