/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
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

#include "theory/strings/array_solver.h"

#include "expr/sequence.h"
#include "theory/strings/arith_entail.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"
#include "util/rational.h"
#include "util/string.h"

using namespace cvc5::context;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

ArraySolver::ArraySolver(Env& env,
                         SolverState& s,
                         InferenceManager& im,
                         TermRegistry& tr,
                         BaseSolver& bs,
                         CoreSolver& cs,
                         ExtfSolver& es,
                         ExtTheory& extt)
    : EnvObj(env),
      d_state(s),
      d_im(im),
      d_termReg(tr),
      d_bsolver(bs),
      d_csolver(cs),
      d_esolver(es),
      d_coreSolver(env, s, im, tr, cs, es, extt),
      d_eqProc(context())
{
  NodeManager* nm = NodeManager::currentNM();
  d_zero = nm->mkConstInt(Rational(0));
}

ArraySolver::~ArraySolver() {}

void ArraySolver::checkArrayConcat()
{
  if (!d_termReg.hasSeqUpdate())
  {
    Trace("seq-array") << "No seq.update/seq.nth terms, skipping check..."
                       << std::endl;
    return;
  }
  d_currTerms.clear();
  Trace("seq-array") << "ArraySolver::checkArrayConcat..." << std::endl;
  // Get the set of relevant terms. The core array solver requires knowing this
  // set to ensure its write model is only over relevant terms.
  std::vector<Node> terms = d_esolver.getRelevantActive();
  checkTerms(terms);
}

void ArraySolver::checkArray()
{
  if (!d_termReg.hasSeqUpdate())
  {
    Trace("seq-array") << "No seq.update/seq.nth terms, skipping check..."
                       << std::endl;
    return;
  }
  Trace("seq-array") << "ArraySolver::checkArray..." << std::endl;
  d_coreSolver.check(d_currTerms[SEQ_NTH], d_currTerms[STRING_UPDATE]);
}

void ArraySolver::checkArrayEager()
{
  if (!d_termReg.hasSeqUpdate())
  {
    Trace("seq-array") << "No seq.update/seq.nth terms, skipping check..."
                       << std::endl;
    return;
  }
  Trace("seq-array") << "ArraySolver::checkArray..." << std::endl;
  // get the set of relevant terms, for reasons described above
  std::vector<Node> terms = d_esolver.getRelevantActive();
  std::vector<Node> nthTerms;
  std::vector<Node> updateTerms;
  for (const Node& n : terms)
  {
    Kind k = n.getKind();
    if (k == STRING_UPDATE)
    {
      updateTerms.push_back(n);
    }
    else if (k == SEQ_NTH)
    {
      nthTerms.push_back(n);
    }
  }
  d_coreSolver.check(nthTerms, updateTerms);
}

void ArraySolver::checkTerms(const std::vector<Node>& terms)
{
  // get all the active update terms that have not been reduced in the
  // current context by context-dependent simplification
  std::unordered_set<Node> processed;
  for (const Node& t : terms)
  {
    bool checkInv = false;
    Kind k = t.getKind();
    Trace("seq-array-debug") << "check term " << t << "..." << std::endl;
    if (k == STRING_UPDATE)
    {
      if (!d_termReg.isHandledUpdateOrSubstr(t))
      {
        // not handled by procedure
        Trace("seq-array-debug") << "...unhandled" << std::endl;
        continue;
      }
      // for update terms, also check the inverse inference
      checkInv = true;
    }
    else if (k != SEQ_NTH)
    {
      continue;
    }

    if (d_bsolver.isCongruent(t))
    {
      continue;
    }

    // check the normal inference
    checkTerm(t, false);
    if (checkInv)
    {
      checkTerm(t, true);
    }
  }
}

void ArraySolver::checkTerm(Node t, bool checkInv)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = t.getKind();
  Node r = d_state.getRepresentative(t[0]);
  Node rself;
  NormalForm& nf = d_csolver.getNormalForm(r);
  Trace("seq-array-debug") << "...normal form " << nf.d_nf << std::endl;
  std::vector<Node> nfChildren;

  if (k == SEQ_NTH)
  {
    // The core solver must process all `nth` terms
    d_currTerms[SEQ_NTH].push_back(t);
  }

  if (checkInv)
  {
    if (k != STRING_UPDATE)
    {
      return;
    }
    // If the term we are updating is atomic, but the update itself
    // not atomic, then we will apply the inverse version of the update
    // concat rule, based on the normal form of the term itself.
    rself = d_state.getRepresentative(t);
    NormalForm& nfSelf = d_csolver.getNormalForm(rself);
    if (nfSelf.d_nf.size() > 1)
    {
      nfChildren.insert(
          nfChildren.end(), nfSelf.d_nf.begin(), nfSelf.d_nf.end());
    }
    else
    {
      return;
    }
  }
  else
  {
    if (nf.d_nf.empty())
    {
      // updates should have been reduced (UPD_EMPTYSTR)
      Assert(k != STRING_UPDATE);
      Trace("seq-array-debug") << "...empty" << std::endl;
      return;
    }
    else if (nf.d_nf.size() == 1)
    {
      Trace("seq-array-debug") << "...norm form size 1" << std::endl;
      // NOTE: could split on n=0 if needed, do not introduce ITE
      Kind ck = nf.d_nf[0].getKind();
      bool cIsConst = nf.d_nf[0].isConst();
      // Note that (seq.unit c) is rewritten to CONST_SEQUENCE{c}, hence we
      // check two cases here. It is important for completeness of this schema
      // to handle this differently from STRINGS_ARRAY_UPDATE_CONCAT /
      // STRINGS_ARRAY_NTH_CONCAT. Otherwise we would conclude a trivial
      // equality when update/nth is applied to a constant of length one.
      if (ck == SEQ_UNIT || ck == STRING_UNIT
          || (cIsConst && Word::getLength(nf.d_nf[0]) == 1))
      {
        Trace("seq-array-debug") << "...unit case" << std::endl;
        // do we know whether n = 0 ?
        // x = (seq.unit m) => (seq.update x n z) = ite(n=0, z, (seq.unit m))
        // x = (seq.unit m) ^ n=0 => (seq.nth x n) = m
        InferenceId iid;
        Node eq;
        std::vector<Node> exp;
        std::vector<Node> nexp;
        d_im.addToExplanation(t[0], nf.d_nf[0], exp);
        d_im.addToExplanation(r, t[0], exp);
        if (k == STRING_UPDATE)
        {
          iid = InferenceId::STRINGS_ARRAY_UPDATE_UNIT;
          eq = nm->mkNode(
              ITE, t[1].eqNode(d_zero), t.eqNode(t[2]), t.eqNode(nf.d_nf[0]));
        }
        else
        {
          if (d_state.areDisequal(t[1], d_zero))
          {
            // n is known to be disequal from zero, skip
            return;
          }
          Assert(k == SEQ_NTH);
          Node val;
          if (cIsConst)
          {
            val = Word::getNth(nf.d_nf[0], 0);
          }
          else
          {
            val = nf.d_nf[0][0];
          }
          iid = InferenceId::STRINGS_ARRAY_NTH_UNIT;
          eq = t.eqNode(val);
          if (t[1] != d_zero)
          {
            exp.push_back(t[1].eqNode(d_zero));
            nexp.push_back(t[1].eqNode(d_zero));
          }
        }
        if (d_eqProc.find(eq) == d_eqProc.end())
        {
          d_eqProc.insert(eq);
          d_im.sendInference(exp, nexp, eq, iid);
        }
        return;
      }
      else if (!cIsConst)
      {
        if (k == STRING_UPDATE)
        {
          // If the term we are updating is atomic, but the update itself
          // not atomic, then we will apply the inverse version of the update
          // concat rule, based on the normal form of the term itself.
          rself = d_state.getRepresentative(t);
          NormalForm& nfSelf = d_csolver.getNormalForm(rself);
          if (nfSelf.d_nf.size() == 1)
          {
            // otherwise, if the normal form is not a constant word, and we
            // are an atomic update term, then this term will be given to the
            // core array solver.
            d_currTerms[k].push_back(t);
          }
        }
        return;
      }
      else
      {
        // if the normal form is a constant word, it is treated as a
        // concatenation. We split per character and case split on whether the
        // nth/update falls on each character below, which must have a size
        // greater than one.
        std::vector<Node> chars = Word::getChars(nf.d_nf[0]);
        Assert(chars.size() > 1);
        nfChildren.insert(nfChildren.end(), chars.begin(), chars.end());
      }
    }
    else
    {
      nfChildren.insert(nfChildren.end(), nf.d_nf.begin(), nf.d_nf.end());
    }
  }
  // otherwise, we are the concatenation of the components
  // NOTE: for nth, split on index vs component lengths, do not introduce ITE
  std::vector<Node> cond;
  std::vector<Node> cchildren;
  std::vector<Node> lacc;
  SkolemCache* skc = d_termReg.getSkolemCache();
  for (const Node& c : nfChildren)
  {
    Trace("seq-array-debug") << "...process " << c << std::endl;
    Node clen = nm->mkNode(STRING_LENGTH, c);
    Node currIndex = t[1];
    Node currSum = d_zero;
    if (!lacc.empty())
    {
      currSum = lacc.size() == 1 ? lacc[0] : nm->mkNode(ADD, lacc);
      currIndex = nm->mkNode(SUB, currIndex, currSum);
    }
    Node cc;
    if (k == STRING_UPDATE && checkInv)
    {
      // component for the reverse form of the update inference is a fresh
      // variable, in particular, the purification variable for the substring
      // of the term we are updating.
      Node sstr = nm->mkNode(STRING_SUBSTR, t[0], currSum, clen);
      cc = skc->mkSkolemCached(sstr, SkolemCache::SkolemId::SK_PURIFY, "z");
    }
    // If it is a constant of length one, then the update/nth is determined
    // in this interval. Notice this is done here as
    // an optimization to short cut introducing terms like
    // (seq.nth (seq.unit c) i), which by construction is only relevant in
    // the context where i = 0, hence we replace by c here.
    else if (c.isConst())
    {
      if (Word::getLength(c) == 1)
      {
        if (k == STRING_UPDATE)
        {
          cc = nm->mkNode(ITE, t[1].eqNode(d_zero), t[2], c);
        }
        else
        {
          cc = Word::getNth(c, 0);
        }
      }
    }
    // if we did not process as a constant of length one
    if (cc.isNull())
    {
      if (k == STRING_UPDATE)
      {
        cc = nm->mkNode(STRING_UPDATE, c, currIndex, t[2]);
      }
      else
      {
        Assert(k == SEQ_NTH);
        cc = nm->mkNode(SEQ_NTH, c, currIndex);
      }
    }
    Trace("seq-array-debug") << "......component " << cc << std::endl;
    cchildren.push_back(cc);
    lacc.push_back(clen);
    if (k == SEQ_NTH)
    {
      Node currSumPost = lacc.size() == 1 ? lacc[0] : nm->mkNode(ADD, lacc);
      Node cf = nm->mkNode(LT, t[1], currSumPost);
      Trace("seq-array-debug") << "......condition " << cf << std::endl;
      cond.push_back(cf);
    }
    else if (k == STRING_UPDATE && checkInv)
    {
      Node ccu = nm->mkNode(STRING_UPDATE, cc, currIndex, t[2]);
      Node eq = c.eqNode(ccu);
      Trace("seq-array-debug") << "......condition " << eq << std::endl;
      cond.push_back(eq);
    }
  }
  // z = (seq.++ x y) =>
  // (seq.update z n l) =
  //   (seq.++ (seq.update x n 1) (seq.update y (- n len(x)) 1))
  // z = (seq.++ x y) ^ (>= n 0) ^ (< n (+ (str.len x) (str.len y)))) =>
  // (seq.nth z n) =
  //    (ite (< n (str.len x)) (seq.nth x n)
  //      (seq.nth y (- n (str.len x))))
  InferenceId iid;
  std::vector<Node> exp;
  std::vector<Node> nexp;
  Node eq;
  if (k == STRING_UPDATE)
  {
    Node finalc = utils::mkConcat(cchildren, t.getType());
    if (checkInv)
    {
      eq = t[0].eqNode(finalc);
      cond.push_back(eq);
      eq = nm->mkAnd(cond);
    }
    else
    {
      eq = t.eqNode(finalc);
    }
    // Must rewrite the equality to ensure terms are in rewritten form. This
    // is important since this inference may be processed as a fact.
    eq = rewrite(eq);
    iid = checkInv ? InferenceId::STRINGS_ARRAY_UPDATE_CONCAT_INVERSE
                   : InferenceId::STRINGS_ARRAY_UPDATE_CONCAT;
  }
  else
  {
    std::reverse(cchildren.begin(), cchildren.end());
    std::reverse(cond.begin(), cond.end());
    eq = t.eqNode(cchildren[0]);
    for (size_t i = 1, ncond = cond.size(); i < ncond; i++)
    {
      eq = nm->mkNode(ITE, cond[i], t.eqNode(cchildren[i]), eq);
    }
    Node inBoundsCond = nm->mkNode(AND, nm->mkNode(GEQ, t[1], d_zero), cond[0]);
    exp.push_back(inBoundsCond);
    nexp.push_back(inBoundsCond);
    iid = InferenceId::STRINGS_ARRAY_NTH_CONCAT;
  }
  if (checkInv)
  {
    NormalForm& nfSelf = d_csolver.getNormalForm(rself);
    exp.insert(exp.end(), nfSelf.d_exp.begin(), nfSelf.d_exp.end());
    d_im.addToExplanation(t, nfSelf.d_base, exp);
  }
  else
  {
    exp.insert(exp.end(), nf.d_exp.begin(), nf.d_exp.end());
    d_im.addToExplanation(t[0], nf.d_base, exp);
  }
  if (d_eqProc.find(eq) == d_eqProc.end())
  {
    d_eqProc.insert(eq);
    Trace("seq-array") << "- send lemma - " << eq << std::endl;
    d_im.sendInference(exp, nexp, eq, iid);
  }
}

const std::map<Node, Node>& ArraySolver::getWriteModel(Node eqc)
{
  return d_coreSolver.getWriteModel(eqc);
}

const std::map<Node, Node>& ArraySolver::getConnectedSequences()
{
  return d_coreSolver.getConnectedSequences();
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
