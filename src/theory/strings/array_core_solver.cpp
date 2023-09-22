/******************************************************************************
 * Top contributors (to current version):
 *   Ying Sheng, Andres Noetzli, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sequences solver for seq.nth/seq.update.
 */

#include "theory/strings/array_core_solver.h"

#include "theory/strings/array_solver.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"
#include "util/rational.h"

using namespace cvc5::context;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

ArrayCoreSolver::ArrayCoreSolver(Env& env,
                                 SolverState& s,
                                 InferenceManager& im,
                                 TermRegistry& tr,
                                 CoreSolver& cs,
                                 ExtfSolver& es,
                                 ExtTheory& extt)
    : EnvObj(env),
      d_state(s),
      d_im(im),
      d_termReg(tr),
      d_csolver(cs),
      d_esolver(es),
      d_extt(extt),
      d_lem(context()),
      d_registeredUpdates(userContext())
{
}

ArrayCoreSolver::~ArrayCoreSolver() {}

void ArrayCoreSolver::sendInference(const std::vector<Node>& exp,
                                    const Node& lem,
                                    const InferenceId iid,
                                    bool asLemma)
{
  if (d_lem.find(lem) == d_lem.end())
  {
    d_lem.insert(lem);
    Trace("seq-update") << "- send lemma - " << lem << std::endl;
    d_im.sendInference(exp, lem, iid, false, asLemma);
  }
}

void ArrayCoreSolver::checkNth(const std::vector<Node>& nthTerms)
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> extractTerms = d_esolver.getActive(STRING_SUBSTR);
  for (const Node& n : extractTerms)
  {
    if (d_termReg.isHandledUpdateOrSubstr(n))
    {
      // (seq.extract A i l) in terms:
      // IF (<= 0 i) ^ (< i (str.len A))
      // THEN (seq.extract A i l) = (seq.unit (seq.nth A i))
      // ELSE (seq.extract A i l) = empty
      std::vector<Node> exp;
      Node cond1 = nm->mkNode(LEQ, nm->mkConstInt(Rational(0)), n[1]);
      Node cond2 = nm->mkNode(LT, n[1], nm->mkNode(STRING_LENGTH, n[0]));
      Node cond = nm->mkNode(AND, cond1, cond2);
      TypeNode tn = n.getType();
      Node nth = nm->mkNode(SEQ_NTH, n[0], n[1]);
      Node unit = utils::mkUnit(tn, nth);
      Node body1 = nm->mkNode(EQUAL, n, unit);
      Node body2 = nm->mkNode(EQUAL, n, Word::mkEmptyWord(n.getType()));
      Node lem = nm->mkNode(ITE, cond, body1, body2);
      sendInference(exp, lem, InferenceId::STRINGS_ARRAY_NTH_EXTRACT);
    }
  }
  for (size_t i = 0; i < nthTerms.size(); i++)
  {
    for (size_t j = i + 1; j < nthTerms.size(); j++)
    {
      TNode x = nthTerms[i][0];
      TNode y = nthTerms[j][0];

      if (x.getType() != y.getType())
      {
        continue;
      }

      TNode n = nthTerms[i][1];
      TNode m = nthTerms[j][1];
      if (d_state.areEqual(n, m) && !d_state.areEqual(x, y)
          && !d_state.areDisequal(x, y))
      {
        d_im.sendSplit(x, y, InferenceId::STRINGS_ARRAY_EQ_SPLIT);
      }
    }
  }
}

void ArrayCoreSolver::checkUpdate(const std::vector<Node>& updateTerms)
{
  NodeManager* nm = NodeManager::currentNM();

  Trace("seq-array-core-debug")
      << "number of update terms: " << updateTerms.size() << std::endl;
  for (const Node& n : updateTerms)
  {
    Trace("seq-array-core-debug") << "check term " << n << std::endl;

    // note that the term could rewrites to a skolem
    // get proxy variable for the update term as t
    Node termProxy = d_termReg.ensureProxyVariableFor(n);

    if (d_registeredUpdates.find(n) == d_registeredUpdates.end())
    {
      Trace("seq-array-core-debug") << "... registering" << std::endl;
      d_registeredUpdates.insert(n);
      // Introduce nth(update(s, n, t), n) for all update(s, n, t) terms.
      //
      // x = update(s, n, t)
      // ------------------------------------------------------------
      // nth(x, n) = ite(n in range(0, len(s)), nth(t, 0), nth(s, n))
      Node left = nm->mkNode(SEQ_NTH, termProxy, n[1]);
      Node cond =
          nm->mkNode(AND,
                     nm->mkNode(GEQ, n[1], nm->mkConstInt(Rational(0))),
                     nm->mkNode(LT, n[1], nm->mkNode(STRING_LENGTH, n[0])));
      Node body1 = nm->mkNode(SEQ_NTH, n[2], nm->mkConstInt(Rational(0)));
      Node body2 = nm->mkNode(SEQ_NTH, n[0], n[1]);
      Node right = nm->mkNode(ITE, cond, body1, body2);
      Node lem = nm->mkNode(EQUAL, left, right);

      std::vector<Node> exp;
      // We don't have to add (termProxy = n) to the explanation, since this
      // is always true and justified by definition. Also note that if lazy
      // term registration is enabled, this equality may not (yet) hold in
      // the equality engine, since termProxy may have been introduced in this
      // call.
      sendInference(
          exp, lem, InferenceId::STRINGS_ARRAY_NTH_TERM_FROM_UPDATE, true);

      // x = update(s, n, t)
      // ------------------------
      // 0 <= n < len(t) and nth(s, n) != nth(update(s, n, t))  and x != s ||
      // x = s
      lem = nm->mkNode(
          OR,
          nm->mkNode(AND,
                     left.eqNode(nm->mkNode(SEQ_NTH, n[0], n[1])).notNode(),
                     n.eqNode(n[0]).negate(),
                     cond),
          n.eqNode(n[0]));
      sendInference(exp, lem, InferenceId::STRINGS_ARRAY_UPDATE_BOUND, true);
    }

    Node rn = d_state.getRepresentative(n);
    Node rs = d_state.getRepresentative(n[0]);
    for (const Node& r : {rn, rs})
    {
      // Enumerate n-th terms for sequences that are related to the current
      // update term
      const std::set<Node>& indexes = d_indexMap[r];
      Trace("seq-array-core-debug") << "  check nth for " << r
                                    << " with indices " << indexes << std::endl;
      Node i = n[1];
      for (Node j : indexes)
      {
        // nth(x, m)
        // y = update(s, n, t)
        // x = y or x = s
        // ------------------------
        // nth(update(s, n, t)) =
        //   ite(0 <= m < len(s),
        //     ite(n = m, nth(t, 0), nth(s, m)),
        //     nth(update(s, n, t), m))
        Node nth = nm->mkNode(SEQ_NTH, termProxy, j);
        Node nthInBounds =
            nm->mkNode(AND,
                       nm->mkNode(LEQ, nm->mkConstInt(0), j),
                       nm->mkNode(LT, j, nm->mkNode(STRING_LENGTH, n[0])));
        Node idxEq = i.eqNode(j);
        Node updateVal = nm->mkNode(SEQ_NTH, n[2], nm->mkConstInt(0));
        Node iteNthInBounds = nm->mkNode(
            ITE, i.eqNode(j), updateVal, nm->mkNode(SEQ_NTH, n[0], j));
        Node rhs = nm->mkNode(ITE, nthInBounds, iteNthInBounds, nth);
        Node lem = nth.eqNode(rhs);

        std::vector<Node> exp;
        d_im.addToExplanation(termProxy, n, exp);
        if (d_state.areEqual(r, n))
        {
          d_im.addToExplanation(r, n, exp);
        }
        else
        {
          Assert(d_state.areEqual(r, n[0]));
          d_im.addToExplanation(r, n[0], exp);
        }
        // rhs is ITE, send as lemma
        sendInference(exp, lem, InferenceId::STRINGS_ARRAY_NTH_UPDATE, true);
      }
    }
  }
}

void ArrayCoreSolver::check(const std::vector<Node>& nthTerms,
                            const std::vector<Node>& updateTerms)
{
  NodeManager* nm = NodeManager::currentNM();

  Trace("seq-array-debug") << "NTH SIZE: " << nthTerms.size() << std::endl;
  if (TraceIsOn("seq-array-terms"))
  {
    for (const Node& n : nthTerms)
    {
      Trace("seq-array-terms") << n << std::endl;
    }
  }
  Trace("seq-array-debug") << "UPDATE SIZE: " << updateTerms.size()
                           << std::endl;
  if (TraceIsOn("seq-array-terms"))
  {
    for (const Node& n : updateTerms)
    {
      Trace("seq-array-terms") << n << std::endl;
    }
  }
  Trace("seq-update") << "SequencesArraySolver::check..." << std::endl;
  d_writeModel.clear();
  d_indexMap.clear();
  for (const Node& n : nthTerms)
  {
    // (seq.nth n[0] n[1])
    Node r = d_state.getRepresentative(n[0]);
    Node ri = d_state.getRepresentative(n[1]);
    Trace("seq-update") << "- " << r << ": " << ri << " -> " << n << std::endl;
    d_writeModel[r][ri] = n;
    d_indexMap[r].insert(ri);

    if (n[0].getKind() == STRING_REV)
    {
      Node s = n[0][0];
      Node i = n[1];
      Node sLen = nm->mkNode(STRING_LENGTH, s);
      Node iRev = nm->mkNode(
          SUB, sLen, nm->mkNode(ADD, i, nm->mkConstInt(Rational(1))));

      std::vector<Node> nexp;
      nexp.push_back(nm->mkNode(LEQ, nm->mkConstInt(Rational(0)), i));
      nexp.push_back(nm->mkNode(LT, i, sLen));

      // 0 <= i ^ i < len(s) => seq.nth(seq.rev(s), i) = seq.nth(s, len(s) - i -
      // 1)
      Node ret = nm->mkNode(SEQ_NTH, s, iRev);
      d_im.sendInference(
          {}, nexp, n.eqNode(ret), InferenceId::STRINGS_ARRAY_NTH_REV);
      d_extt.markInactive(n, ExtReducedId::STRINGS_NTH_REV);
    }
  }
  checkNth(nthTerms);
  checkUpdate(updateTerms);
  // compute connected sequences
  if (!d_im.hasSent())
  {
    computeConnected(updateTerms);
  }
}

void ArrayCoreSolver::computeConnected(const std::vector<Node>& updateTerms)
{
  d_connectedSeq.clear();
  std::map<Node, Node> conTmp;
  std::map<Node, Node>::iterator it;
  for (const Node& n : updateTerms)
  {
    Node newRep;
    for (size_t i = 0; i < 2; i++)
    {
      Node s = i == 0 ? n[0] : n;
      TNode r = d_state.getRepresentative(s);
      // get the find
      it = conTmp.find(r);
      while (it != conTmp.end())
      {
        r = it->second;
        it = conTmp.find(r);
      }
      if (i == 0)
      {
        newRep = r;
      }
      else if (newRep != r)
      {
        conTmp[newRep] = r;
      }
    }
  }
  // go back and normalize the find to representatives
  for (std::pair<const Node, Node>& c : conTmp)
  {
    TNode r = c.first;
    it = conTmp.find(r);
    while (it != conTmp.end())
    {
      r = it->second;
      it = conTmp.find(r);
    }
    d_connectedSeq[c.first] = r;
  }
}

const std::map<Node, Node>& ArrayCoreSolver::getWriteModel(Node eqc)
{
  if (TraceIsOn("seq-write-model"))
  {
    Trace("seq-write-model") << "write model of " << eqc << ":" << std::endl;
    for (auto& x : d_writeModel[eqc])
    {
      Trace("seq-write-model") << x.first << ": " << x.second << std::endl;
    }
  }
  return d_writeModel[eqc];
}

const std::map<Node, Node>& ArrayCoreSolver::getConnectedSequences()
{
  return d_connectedSeq;
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
