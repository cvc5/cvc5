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

#include "theory/strings/sequences_update_solver.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"
#include "util/rational.h"

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

void SequencesArraySolver::sendInference(const std::vector<Node>& exp,
                                         const Node& lem)
{
  if (d_lem.find(lem) == d_lem.end())
  {
    d_lem.insert(lem);
    InferenceId iid = InferenceId::STRINGS_SU_UPDATE_UNIT;
    Trace("seq-update") << "- send lemma - " << lem << std::endl;
    d_im.sendInference(exp, lem, iid);
  }
}

void SequencesArraySolver::checkNth(const std::vector<Node>& nthTerms)
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> extractTerms = d_esolver.getActive(STRING_SUBSTR);
  for (const Node& n : extractTerms)
  {
    if (SequencesUpdateSolver::isHandledUpdate(n))
    {
      // (seq.extract A i l) ^ (<= 0 i) ^ (< i (str.len A)) --> (seq.unit
      // (seq.nth A i))
      std::vector<Node> exp;
      Node cond1 = nm->mkNode(LEQ, nm->mkConst(Rational(0)), n[1]);
      Node cond2 = nm->mkNode(LT, n[1], nm->mkNode(STRING_LENGTH, n[0]));
      Node cond = nm->mkNode(AND, cond1, cond2);
      Node body1 = nm->mkNode(
          EQUAL, n, nm->mkNode(SEQ_UNIT, nm->mkNode(SEQ_NTH, n[0], n[1])));
      Node body2 = nm->mkNode(EQUAL, n, Word::mkEmptyWord(n.getType()));
      Node lem = nm->mkNode(ITE, cond, body1, body2);
      sendInference(exp, lem);
    }
  }
}

void SequencesArraySolver::checkUpdate(const std::vector<Node>& updateTerms)
{
  NodeManager * nm = NodeManager::currentNM();

  Trace("seq-array-debug") << "updateTerms number: " <<  updateTerms.size() << std::endl;
  for (const Node& n : updateTerms)
  {
    // current term (seq.update x i a)
    
    // inference rule is:
    // (seq.update x i a) in TERMS     
    // (seq.nth t j) in TERMS  
    // t == (seq.update x i a)
    // ----------------------------------------------------------------------
    // (seq.nth (seq.update x i a) j) = 
    //   (ITE, j in range(i, i+len(a)), (seq.nth a (j - i)),  (seq.nth x j))
    
    // t == (seq.update x i a) =>
    // (seq.nth t j) = (ITE, j in range(i, i+len(a)), (seq.nth a (j - i)),
    // (seq.nth x j))

    // note that the term could rewrites to a skolem
    // get proxy variable for the update term as t
    Node termProxy = d_termReg.getProxyVariableFor(n);
    Trace("seq-update") << "- " << termProxy << " = " << n << std::endl;
    std::vector<Node> exp;
    d_im.addToExplanation(termProxy, n, exp);

    // optimization: add a short cut t == (seq.update n[0] n[1] n[2]) => t[i] ==
    // n[2][0]
    Node left = nm->mkNode(SEQ_NTH, termProxy, n[1]);
    Node right =
        nm->mkNode(SEQ_NTH, n[2], nm->mkConst(Rational(0)));  // n[2][0]
    right = Rewriter::rewrite(right);
    Node lem = nm->mkNode(EQUAL, left, right);
    Trace("seq-array-debug") << "enter" << std::endl;
    sendInference(exp, lem);

    // enumerate possible index
    for (auto nth : d_index_map)
    {
      Node seq = nth.first;
      if (d_state.areEqual(seq, n) || d_state.areEqual(seq, n[0]))
      {
        std::set<Node> indexes = nth.second;
        for (Node j : indexes)
        {
          // optimization: add a short cut for special case (seq.update n[0]
          // n[1] (seq.unit e))
          if (n[2].getKind() == SEQ_UNIT)
          {
            left = nm->mkNode(DISTINCT, n[1], j);
            Node nth1 = nm->mkNode(SEQ_NTH, termProxy, j);
            Node nth2 = nm->mkNode(SEQ_NTH, n[0], j);
            right = nm->mkNode(EQUAL, nth1, nth2);
            lem = nm->mkNode(IMPLIES, left, right);
            sendInference(exp, lem);
          }

          // normal cases
          left = nm->mkNode(SEQ_NTH, termProxy, j);
          Node cond = nm->mkNode(
              AND,
              nm->mkNode(LEQ, n[1], j),
              nm->mkNode(
                  LT,
                  j,
                  nm->mkNode(PLUS, n[1], nm->mkNode(STRING_LENGTH, n[2]))));
          Node body1 = nm->mkNode(SEQ_NTH, n[2], nm->mkNode(MINUS, j, n[1]));
          Node body2 = nm->mkNode(SEQ_NTH, n[0], j);
          right = nm->mkNode(ITE, cond, body1, body2);
          lem = nm->mkNode(EQUAL, left, right);
          sendInference(exp, lem);
        }
      }
    }
  }
}

void SequencesArraySolver::check(const std::vector<Node>& nthTerms,
                                 const std::vector<Node>& updateTerms)
{
  NodeManager* nm = NodeManager::currentNM();

  Trace("seq-array-debug") << "NTH SIZE: " << nthTerms.size() << std::endl;
  for (const Node& n : nthTerms)
  {
    Trace("seq-array-terms") << n << std::endl;
  }
  Trace("seq-array-debug") << "UPDATE SIZE: " << updateTerms.size() << std::endl;
  for (const Node& n : updateTerms)
  {
    Trace("seq-array-terms") << n << std::endl;
  }
  Trace("seq-update") << "SequencesArraySolver::check..." << std::endl;
  d_writeModel.clear();
  for (const Node& n : nthTerms)
  {
    // (seq.nth n[0] n[1])
    Node r = d_state.getRepresentative(n[0]);
    Trace("seq-update") << "- " << r << ": " << n[1] << " -> " << n
                        << std::endl;
    d_writeModel[r][n[1]] = n;
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
  checkNth(nthTerms);
  checkUpdate(updateTerms);
}

const std::map<Node, Node>& SequencesArraySolver::getWriteModel(Node eqc)
{
  return d_writeModel[eqc];
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5
