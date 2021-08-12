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

#include "theory/strings/sequences_update_solver.h"

#include "util/rational.h"
#include "theory/strings/arith_entail.h"
#include "theory/strings/theory_strings_utils.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace strings {

SequencesUpdateSolver::SequencesUpdateSolver(SolverState& s,
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
      d_sasolver(s, im, tr, cs, es, extt),
      d_eqProc(s.getSatContext())
{
  NodeManager * nm = NodeManager::currentNM();
  d_zero = nm->mkConst(Rational(0));
}

SequencesUpdateSolver::~SequencesUpdateSolver() {}

bool SequencesUpdateSolver::isHandledUpdate(Node n)
{
  Assert (n.getKind()==STRING_UPDATE);
  NodeManager * nm = NodeManager::currentNM();
  Node lenN = nm->mkNode(STRING_LENGTH, n[2]);
  Node one = nm->mkConst(Rational(1));
  return ArithEntail::checkEq(lenN, one);
}

Node SequencesUpdateSolver::getUpdateBase(Node n)
{
  while (n.getKind()==STRING_UPDATE)
  {
    n = n[0];
  }
  return n;
}

void SequencesUpdateSolver::checkArrayConcat()
{
  if (!d_termReg.hasSeqUpdate())
  {
    Trace("seq-update") << "No seq.update/seq.nth terms, skipping check..."
                        << std::endl;
    return;
  }
  d_currTerms.clear();
  Trace("seq-update") << "SequencesUpdateSolver::checkArrayConcat..." << std::endl;
  checkTerms(STRING_UPDATE);
  checkTerms(SEQ_NTH);
}
void SequencesUpdateSolver::checkArray()
{
  if (!d_termReg.hasSeqUpdate())
  {
    Trace("seq-update") << "No seq.update/seq.nth terms, skipping check..."
                        << std::endl;
    return;
  }
  Trace("seq-update") << "SequencesUpdateSolver::checkArray..." << std::endl;
  d_sasolver.check(d_currTerms[SEQ_NTH], d_currTerms[STRING_UPDATE]);
}
  
void SequencesUpdateSolver::checkTerms(Kind k)
{
  Assert (k==STRING_UPDATE || k==SEQ_NTH);
  NodeManager * nm = NodeManager::currentNM();
  // get all the active update terms that have not been reduced in the
  // current context by context-dependent simplification
  std::vector<Node> terms = d_esolver.getActive(k);
  for (const Node& t : terms)
  {
    Trace("seq-update-debug") << "check term " << t << "..." << std::endl;
    Assert (t.getKind()==k);
    if (k==STRING_UPDATE && !isHandledUpdate(t))
    {
      // not handled by procedure
      Trace("seq-update-debug") << "...unhandled" << std::endl;
      continue;
    }
    Node r = d_state.getRepresentative(t[0]);
    NormalForm& nf = d_csolver.getNormalForm(r);
    Trace("seq-update-debug") << "...normal form " << nf.d_nf << std::endl;
    if (nf.d_nf.empty())
    {
      // should have been reduced (UPD_EMPTYSTR)
      if (k==STRING_UPDATE) Assert (false);
      Trace("seq-update-debug") << "...empty" << std::endl;
      continue;
    }
    else if (nf.d_nf.size() == 1)
    {
      // TODO: split on n=0 if needed, do not introduce ITE
      if (nf.d_nf[0].getKind() == SEQ_UNIT)
      {
        // do we know whether n = 0 ?
        // x = (seq.unit m) => (seq.update x n z) = ite(n=0, z, (seq.unit m))
        // x = (seq.unit m) => (seq.nth x n) = ite(n=0, m, Uf(x, n))
        Node thenBranch;
        Node elseBranch;
        InferenceId iid;
        if (k==STRING_UPDATE)
        {
          thenBranch = t[2];
          elseBranch = nf.d_nf[0];
          iid = InferenceId::STRINGS_SU_UPDATE_UNIT;
        }
        else
        {
          Assert (k==SEQ_NTH);
          thenBranch = nf.d_nf[0][0];
          Node uf = SkolemCache::mkSkolemSeqNth(t[0].getType(), "Uf");
          elseBranch = nm->mkNode(APPLY_UF, uf, t[0], t[1]);
          iid = InferenceId::STRINGS_SU_NTH_UNIT;
        }
        std::vector<Node> exp;
        d_im.addToExplanation(t[0], nf.d_nf[0], exp);
        Node eq = nm->mkNode(ITE, t[1].eqNode(d_zero), t.eqNode(thenBranch), t.eqNode(elseBranch));
        if (d_eqProc.find(eq) == d_eqProc.end())
        {
          d_eqProc.insert(eq);
          d_im.sendInference(exp, eq, iid);
        }
        // d_im.sendInference(exp, eq, iid);
      }
      // otherwise, the equivalence class is pure wrt concatenation
      d_currTerms[k].push_back(t);
      continue;
    }
    // otherwise, we are the concatenation of the components
    // TODO: for nth, split on index vs component lengths, do not introduce ITE
    std::vector<Node> cond;
    std::vector<Node> cchildren;
    std::vector<Node> lacc;
    for (const Node& c : nf.d_nf)
    {
      Trace("seq-update-debug") << "...process " << c << std::endl;
      Node clen = nm->mkNode(STRING_LENGTH, c);
      Node currIndex = t[1];
      if (!lacc.empty())
      {
        Node currSum = lacc.size()==1 ? lacc[0] : nm->mkNode(PLUS, lacc);
        currIndex = nm->mkNode(MINUS, currIndex, currSum);
      }
      if (k==STRING_UPDATE)
      {
        Node cc = nm->mkNode(STRING_UPDATE, c, currIndex, t[2]);
        Trace("seq-update-debug") << "......component " << cc << std::endl;
        cchildren.push_back(cc);
      }
      else
      {
        Assert (k==SEQ_NTH);
        Node cc = nm->mkNode(SEQ_NTH, c, currIndex);
        Trace("seq-update-debug") << "......component " << cc << std::endl;
        cchildren.push_back(cc);
      }
      lacc.push_back(clen);
      if (k==SEQ_NTH)
      {
        Node currSumPost = lacc.size()==1 ? lacc[0] : nm->mkNode(PLUS, lacc);
        Node cc = nm->mkNode(LT, t[1], currSumPost);
        Trace("seq-update-debug") << "......condition " << cc << std::endl;
        cond.push_back(cc);
      }
    }
    // z = (seq.++ x y) => 
    // (seq.update z n l) = 
    //   (seq.++ (seq.update x n 1) (seq.update y (- n len(x)) 1))
    // z = (seq.++ x y) =>
    // (seq.nth z n) = 
    //    (ite (or (< n 0) (>= n (+ (str.len x) (str.len y)))) (Uf z n) 
    //    (ite (< n (str.len x)) (seq.nth x n) 
    //      (seq.nth y (- n (str.len x)))))
    InferenceId iid;
    Node eq;
    if (k==STRING_UPDATE)
    {
      Node finalc = utils::mkConcat(cchildren, t.getType());
      eq = t.eqNode(finalc);
      iid = InferenceId::STRINGS_SU_UPDATE_CONCAT;
    }
    else
    {
      std::reverse(cchildren.begin(), cchildren.end());
      std::reverse(cond.begin(), cond.end());
      Node uf = SkolemCache::mkSkolemSeqNth(t[0].getType(), "Uf");
      eq = t.eqNode(cchildren[0]);
      for (size_t i=1, ncond = cond.size(); i<ncond; i++)
      {
        eq = nm->mkNode(ITE, cond[i], t.eqNode(cchildren[i]), eq);
      }
      Node ufa = nm->mkNode(APPLY_UF, uf, t[0], t[1]);
      Node oobCond =
          nm->mkNode(OR, nm->mkNode(LT, t[1], d_zero), cond[0].notNode());
      eq = nm->mkNode(ITE, oobCond, t.eqNode(ufa), eq);
      iid = InferenceId::STRINGS_SU_NTH_CONCAT;
    }
    std::vector<Node> exp;
    exp.insert(exp.end(), nf.d_exp.begin(), nf.d_exp.end());
    exp.push_back(t[0].eqNode(nf.d_base));
    if (d_eqProc.find(eq) == d_eqProc.end())
    {
      d_eqProc.insert(eq);
      Trace("seq-update") << "- send lemma - " << eq << std::endl;
      d_im.sendInference(exp, eq, iid);
    }
  }
}

const std::map<Node, Node>& SequencesUpdateSolver::getWriteModel(Node eqc)
{
  return d_sasolver.getWriteModel(eqc);
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5
