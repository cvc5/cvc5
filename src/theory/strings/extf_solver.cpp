/*********************                                                        */
/*! \file extf_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of solver for extended functions of theory of strings.
 **/

#include "theory/strings/extf_solver.h"

#include "options/strings_options.h"
#include "theory/strings/sequences_rewriter.h"
#include "theory/strings/theory_strings_preprocess.h"
#include "theory/strings/theory_strings_utils.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

ExtfSolver::ExtfSolver(SolverState& s,
                       InferenceManager& im,
                       TermRegistry& tr,
                       StringsRewriter& rewriter,
                       BaseSolver& bs,
                       CoreSolver& cs,
                       ExtTheory& et,
                       SequencesStatistics& statistics)
    : d_state(s),
      d_im(im),
      d_termReg(tr),
      d_rewriter(rewriter),
      d_bsolver(bs),
      d_csolver(cs),
      d_extt(et),
      d_statistics(statistics),
      d_preproc(d_termReg.getSkolemCache(), s.getUserContext(), statistics),
      d_hasExtf(s.getSatContext(), false),
      d_extfInferCache(s.getSatContext()),
      d_reduced(s.getUserContext())
{
  d_extt.addFunctionKind(kind::STRING_SUBSTR);
  d_extt.addFunctionKind(kind::STRING_UPDATE);
  d_extt.addFunctionKind(kind::STRING_STRIDOF);
  d_extt.addFunctionKind(kind::STRING_ITOS);
  d_extt.addFunctionKind(kind::STRING_STOI);
  d_extt.addFunctionKind(kind::STRING_STRREPL);
  d_extt.addFunctionKind(kind::STRING_STRREPLALL);
  d_extt.addFunctionKind(kind::STRING_REPLACE_RE);
  d_extt.addFunctionKind(kind::STRING_REPLACE_RE_ALL);
  d_extt.addFunctionKind(kind::STRING_STRCTN);
  d_extt.addFunctionKind(kind::STRING_IN_REGEXP);
  d_extt.addFunctionKind(kind::STRING_LEQ);
  d_extt.addFunctionKind(kind::STRING_TO_CODE);
  d_extt.addFunctionKind(kind::STRING_TOLOWER);
  d_extt.addFunctionKind(kind::STRING_TOUPPER);
  d_extt.addFunctionKind(kind::STRING_REV);
  d_extt.addFunctionKind(kind::SEQ_UNIT);

  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

ExtfSolver::~ExtfSolver() {}

void ExtfSolver::addSharedTerm(TNode n) { d_extt.registerTermRec(n); }

bool ExtfSolver::doReduction(int effort, Node n)
{
  Assert(d_extfInfoTmp.find(n) != d_extfInfoTmp.end());
  if (!d_extfInfoTmp[n].d_modelActive)
  {
    // n is not active in the model, no need to reduce
    return false;
  }
  if (d_reduced.find(n)!=d_reduced.end())
  {
    // already sent a reduction lemma
    return false;
  }
  // determine the effort level to process the extf at
  // 0 - at assertion time, 1+ - after no other reduction is applicable
  int r_effort = -1;
  // polarity : 1 true, -1 false, 0 neither
  int pol = 0;
  Kind k = n.getKind();
  if (n.getType().isBoolean() && !d_extfInfoTmp[n].d_const.isNull())
  {
    pol = d_extfInfoTmp[n].d_const.getConst<bool>() ? 1 : -1;
  }
  if (k == STRING_STRCTN)
  {
    if (pol == 1)
    {
      r_effort = 1;
    }
    else if (pol == -1)
    {
      if (effort == 2)
      {
        Node x = n[0];
        Node s = n[1];
        std::vector<Node> lexp;
        Node lenx = d_state.getLength(x, lexp);
        Node lens = d_state.getLength(s, lexp);
        if (d_state.areEqual(lenx, lens))
        {
          Trace("strings-extf-debug")
              << "  resolve extf : " << n
              << " based on equal lengths disequality." << std::endl;
          // We can reduce negative contains to a disequality when lengths are
          // equal. In other words, len( x ) = len( s ) implies
          //   ~contains( x, s ) reduces to x != s.
          if (!d_state.areDisequal(x, s))
          {
            // len( x ) = len( s ) ^ ~contains( x, s ) => x != s
            lexp.push_back(lenx.eqNode(lens));
            lexp.push_back(n.negate());
            Node xneqs = x.eqNode(s).negate();
            d_im.sendInference(
                lexp, xneqs, Inference::CTN_NEG_EQUAL, false, true);
          }
          // this depends on the current assertions, so this
          // inference is context-dependent
          d_extt.markReduced(n, true);
          return true;
        }
        else
        {
          r_effort = 2;
        }
      }
    }
  }
  else if (k == STRING_SUBSTR)
  {
    r_effort = 1;
  }
  else if (k == SEQ_UNIT)
  {
    // never necessary to reduce seq.unit
    return false;
  }
  else if (k != STRING_IN_REGEXP)
  {
    r_effort = 2;
  }
  if (effort != r_effort)
  {
    // not the right effort level to reduce
    return false;
  }
  Node c_n = pol == -1 ? n.negate() : n;
  Trace("strings-process-debug")
      << "Process reduction for " << n << ", pol = " << pol << std::endl;
  if (k == STRING_STRCTN && pol == 1)
  {
    Node x = n[0];
    Node s = n[1];
    // positive contains reduces to a equality
    SkolemCache* skc = d_termReg.getSkolemCache();
    Node eq = d_termReg.eagerReduce(n, skc);
    Assert(!eq.isNull());
    Assert(eq.getKind() == ITE && eq[0] == n);
    eq = eq[1];
    std::vector<Node> expn;
    expn.push_back(n);
    d_im.sendInference(expn, expn, eq, Inference::CTN_POS, false, true);
    Trace("strings-extf-debug")
        << "  resolve extf : " << n << " based on positive contain reduction."
        << std::endl;
    Trace("strings-red-lemma") << "Reduction (positive contains) lemma : " << n
                               << " => " << eq << std::endl;
    // context-dependent because it depends on the polarity of n itself
    d_extt.markReduced(n, true);
  }
  else if (k != kind::STRING_TO_CODE)
  {
    NodeManager* nm = NodeManager::currentNM();
    Assert(k == STRING_SUBSTR || k == STRING_UPDATE || k == STRING_STRCTN
           || k == STRING_STRIDOF || k == STRING_ITOS || k == STRING_STOI
           || k == STRING_STRREPL || k == STRING_STRREPLALL
           || k == STRING_REPLACE_RE || k == STRING_REPLACE_RE_ALL
           || k == STRING_LEQ || k == STRING_TOLOWER || k == STRING_TOUPPER
           || k == STRING_REV);
    std::vector<Node> new_nodes;
    Node res = d_preproc.simplify(n, new_nodes);
    Assert(res != n);
    new_nodes.push_back(n.eqNode(res));
    Node nnlem =
        new_nodes.size() == 1 ? new_nodes[0] : nm->mkNode(AND, new_nodes);
    Trace("strings-red-lemma")
        << "Reduction_" << effort << " lemma : " << nnlem << std::endl;
    Trace("strings-red-lemma") << "...from " << n << std::endl;
    d_im.sendInference(d_emptyVec, nnlem, Inference::REDUCTION, false, true);
    Trace("strings-extf-debug")
        << "  resolve extf : " << n << " based on reduction." << std::endl;
    // add as reduction lemma
    d_reduced.insert(n);
  }
  return true;
}

void ExtfSolver::checkExtfReductions(int effort)
{
  // Notice we don't make a standard call to ExtTheory::doReductions here,
  // since certain optimizations like context-dependent reductions and
  // stratifying effort levels are done in doReduction below.
  std::vector<Node> extf = d_extt.getActive();
  Trace("strings-process") << "  checking " << extf.size() << " active extf"
                           << std::endl;
  for (const Node& n : extf)
  {
    Assert(!d_state.isInConflict());
    Trace("strings-process")
        << "  check " << n
        << ", active in model=" << d_extfInfoTmp[n].d_modelActive << std::endl;
    bool ret = doReduction(effort, n);
    if (ret)
    {
      // we do not mark as reduced, since we may want to evaluate
      if (d_im.hasProcessed())
      {
        return;
      }
    }
  }
}

void ExtfSolver::checkExtfEval(int effort)
{
  Trace("strings-extf-list")
      << "Active extended functions, effort=" << effort << " : " << std::endl;
  d_extfInfoTmp.clear();
  NodeManager* nm = NodeManager::currentNM();
  bool has_nreduce = false;
  std::vector<Node> terms = d_extt.getActive();
  // the set of terms we have done extf inferences for
  std::unordered_set<Node, NodeHashFunction> inferProcessed;
  for (const Node& n : terms)
  {
    // Setup information about n, including if it is equal to a constant.
    ExtfInfoTmp& einfo = d_extfInfoTmp[n];
    Node r = d_state.getRepresentative(n);
    einfo.d_const = d_bsolver.getConstantEqc(r);
    // Get the current values of the children of n.
    // Notice that we look up the value of the direct children of n, and not
    // their free variables. In other words, given a term:
    //   t = (str.replace "B" (str.replace x "A" "B") "C")
    // we may build the explanation that:
    //   ((str.replace x "A" "B") = "B") => t = (str.replace "B" "B" "C")
    // instead of basing this on the free variable x:
    //   (x = "A") => t = (str.replace "B" (str.replace "A" "A" "B") "C")
    // Although both allow us to infer t = "C", it is important to use the
    // first kind of inference since it ensures that its subterms have the
    // expected values. Otherwise, we may in rare cases fail to realize that
    // the subterm (str.replace x "A" "B") does not currently have the correct
    // value, say in this example that (str.replace x "A" "B") != "B".
    std::vector<Node> exp;
    std::vector<Node> schildren;
    bool schanged = false;
    for (const Node& nc : n)
    {
      Node sc = getCurrentSubstitutionFor(effort, nc, exp);
      schildren.push_back(sc);
      schanged = schanged || sc != nc;
    }
    // If there is information involving the children, attempt to do an
    // inference and/or mark n as reduced.
    bool reduced = false;
    Node to_reduce = n;
    if (schanged)
    {
      Node sn = nm->mkNode(n.getKind(), schildren);
      Trace("strings-extf-debug")
          << "Check extf " << n << " == " << sn
          << ", constant = " << einfo.d_const << ", effort=" << effort << "..."
          << std::endl;
      einfo.d_exp.insert(einfo.d_exp.end(), exp.begin(), exp.end());
      // inference is rewriting the substituted node
      Node nrc = Rewriter::rewrite(sn);
      // if rewrites to a constant, then do the inference and mark as reduced
      if (nrc.isConst())
      {
        if (effort < 3)
        {
          d_extt.markReduced(n);
          Trace("strings-extf-debug")
              << "  resolvable by evaluation..." << std::endl;
          std::vector<Node> exps;
          // The following optimization gets the "symbolic definition" of
          // an extended term. The symbolic definition of a term t is a term
          // t' where constants are replaced by their corresponding proxy
          // variables.
          // For example, if lsym is a proxy variable for "", then
          // str.replace( lsym, lsym, lsym ) is the symbolic definition for
          // str.replace( "", "", "" ). It is generally better to use symbolic
          // definitions when doing cd-rewriting for the purpose of minimizing
          // clauses, e.g. we infer the unit equality:
          //    str.replace( lsym, lsym, lsym ) == ""
          // instead of making this inference multiple times:
          //    x = "" => str.replace( x, x, x ) == ""
          //    y = "" => str.replace( y, y, y ) == ""
          Trace("strings-extf-debug")
              << "  get symbolic definition..." << std::endl;
          Node nrs;
          // only use symbolic definitions if option is set
          if (options::stringInferSym())
          {
            nrs = d_termReg.getSymbolicDefinition(sn, exps);
          }
          if (!nrs.isNull())
          {
            Trace("strings-extf-debug")
                << "  rewrite " << nrs << "..." << std::endl;
            Node nrsr = Rewriter::rewrite(nrs);
            // ensure the symbolic form is not rewritable
            if (nrsr != nrs)
            {
              // we cannot use the symbolic definition if it rewrites
              Trace("strings-extf-debug")
                  << "  symbolic definition is trivial..." << std::endl;
              nrs = Node::null();
            }
          }
          else
          {
            Trace("strings-extf-debug")
                << "  could not infer symbolic definition." << std::endl;
          }
          Node conc;
          if (!nrs.isNull())
          {
            Trace("strings-extf-debug")
                << "  symbolic def : " << nrs << std::endl;
            if (!d_state.areEqual(nrs, nrc))
            {
              // infer symbolic unit
              if (n.getType().isBoolean())
              {
                conc = nrc == d_true ? nrs : nrs.negate();
              }
              else
              {
                conc = nrs.eqNode(nrc);
              }
              einfo.d_exp.clear();
            }
          }
          else
          {
            if (!d_state.areEqual(n, nrc))
            {
              if (n.getType().isBoolean())
              {
                if (d_state.areEqual(n, nrc == d_true ? d_false : d_true))
                {
                  einfo.d_exp.push_back(nrc == d_true ? n.negate() : n);
                  conc = d_false;
                }
                else
                {
                  conc = nrc == d_true ? n : n.negate();
                }
              }
              else
              {
                conc = n.eqNode(nrc);
              }
            }
          }
          if (!conc.isNull())
          {
            Trace("strings-extf")
                << "  resolve extf : " << sn << " -> " << nrc << std::endl;
            Inference inf = effort == 0 ? Inference::EXTF : Inference::EXTF_N;
            d_im.sendInference(einfo.d_exp, conc, inf, false, true);
            d_statistics.d_cdSimplifications << n.getKind();
            if (d_state.isInConflict())
            {
              Trace("strings-extf-debug") << "  conflict, return." << std::endl;
              return;
            }
          }
        }
        else
        {
          // check if it is already equal, if so, mark as reduced. Otherwise, do
          // nothing.
          if (d_state.areEqual(n, nrc))
          {
            Trace("strings-extf")
                << "  resolved extf, since satisfied by model: " << n
                << std::endl;
            einfo.d_modelActive = false;
          }
        }
        reduced = true;
      }
      else
      {
        // if this was a predicate which changed after substitution + rewriting
        if (!einfo.d_const.isNull() && nrc.getType().isBoolean() && nrc != n)
        {
          bool pol = einfo.d_const == d_true;
          Node nrcAssert = pol ? nrc : nrc.negate();
          Node nAssert = pol ? n : n.negate();
          Assert(effort < 3);
          einfo.d_exp.push_back(nAssert);
          Trace("strings-extf-debug") << "  decomposable..." << std::endl;
          Trace("strings-extf") << "  resolve extf : " << sn << " -> " << nrc
                                << ", const = " << einfo.d_const << std::endl;
          // We send inferences internal here, which may help show unsat.
          // However, we do not make a determination whether n can be marked
          // reduced since this argument may be circular: we may infer than n
          // can be reduced to something else, but that thing may argue that it
          // can be reduced to n, in theory.
          Inference infer =
              effort == 0 ? Inference::EXTF_D : Inference::EXTF_D_N;
          d_im.sendInternalInference(einfo.d_exp, nrcAssert, infer);
        }
        to_reduce = nrc;
      }
    }
    // We must use the original n here to avoid circular justifications for
    // why extended functions are reduced. In particular, n should never be a
    // duplicate of another term considered in the block of code for
    // checkExtfInference below.
    // if not reduced and not processed
    if (!reduced && !n.isNull()
        && inferProcessed.find(n) == inferProcessed.end())
    {
      inferProcessed.insert(n);
      Assert(effort < 3);
      if (effort == 1)
      {
        Trace("strings-extf")
            << "  cannot rewrite extf : " << to_reduce << std::endl;
      }
      // we take to_reduce to be the (partially) reduced version of n, which
      // is justified by the explanation in einfo.
      checkExtfInference(n, to_reduce, einfo, effort);
      if (Trace.isOn("strings-extf-list"))
      {
        Trace("strings-extf-list") << "  * " << to_reduce;
        if (!einfo.d_const.isNull())
        {
          Trace("strings-extf-list") << ", const = " << einfo.d_const;
        }
        if (n != to_reduce)
        {
          Trace("strings-extf-list") << ", from " << n;
        }
        Trace("strings-extf-list") << std::endl;
      }
      if (d_extt.isActive(n) && einfo.d_modelActive)
      {
        has_nreduce = true;
      }
    }
  }
  d_hasExtf = has_nreduce;
}

void ExtfSolver::checkExtfInference(Node n,
                                    Node nr,
                                    ExtfInfoTmp& in,
                                    int effort)
{
  if (in.d_const.isNull())
  {
    return;
  }
  NodeManager* nm = NodeManager::currentNM();
  Trace("strings-extf-infer") << "checkExtfInference: " << n << " : " << nr
                              << " == " << in.d_const << std::endl;

  // add original to explanation
  if (n.getType().isBoolean())
  {
    // if Boolean, it's easy
    in.d_exp.push_back(in.d_const.getConst<bool>() ? n : n.negate());
  }
  else
  {
    // otherwise, must explain via base node
    Node r = d_state.getRepresentative(n);
    // explain using the base solver
    d_bsolver.explainConstantEqc(n, r, in.d_exp);
  }

  // d_extfInferCache stores whether we have made the inferences associated
  // with a node n,
  // this may need to be generalized if multiple inferences apply

  if (nr.getKind() == STRING_STRCTN)
  {
    Assert(in.d_const.isConst());
    bool pol = in.d_const.getConst<bool>();
    if ((pol && nr[1].getKind() == STRING_CONCAT)
        || (!pol && nr[0].getKind() == STRING_CONCAT))
    {
      // If str.contains( x, str.++( y1, ..., yn ) ),
      //   we may infer str.contains( x, y1 ), ..., str.contains( x, yn )
      // The following recognizes two situations related to the above reasoning:
      // (1) If ~str.contains( x, yi ) holds for some i, we are in conflict,
      // (2) If str.contains( x, yj ) already holds for some j, then the term
      // str.contains( x, yj ) is irrelevant since it is satisfied by all models
      // for str.contains( x, str.++( y1, ..., yn ) ).

      // Notice that the dual of the above reasoning also holds, i.e.
      // If ~str.contains( str.++( x1, ..., xn ), y ),
      //   we may infer ~str.contains( x1, y ), ..., ~str.contains( xn, y )
      // This is also handled here.
      if (d_extfInferCache.find(nr) == d_extfInferCache.end())
      {
        d_extfInferCache.insert(nr);

        int index = pol ? 1 : 0;
        std::vector<Node> children;
        children.push_back(nr[0]);
        children.push_back(nr[1]);
        for (const Node& nrc : nr[index])
        {
          children[index] = nrc;
          Node conc = nm->mkNode(STRING_STRCTN, children);
          conc = Rewriter::rewrite(pol ? conc : conc.negate());
          // check if it already (does not) hold
          if (d_state.hasTerm(conc))
          {
            if (d_state.areEqual(conc, d_false))
            {
              // we are in conflict
              d_im.sendInference(in.d_exp, conc, Inference::CTN_DECOMPOSE);
            }
            else if (d_extt.hasFunctionKind(conc.getKind()))
            {
              // can mark as reduced, since model for n implies model for conc
              d_extt.markReduced(conc);
            }
          }
        }
      }
    }
    else
    {
      if (std::find(d_extfInfoTmp[nr[0]].d_ctn[pol].begin(),
                    d_extfInfoTmp[nr[0]].d_ctn[pol].end(),
                    nr[1])
          == d_extfInfoTmp[nr[0]].d_ctn[pol].end())
      {
        Trace("strings-extf-debug") << "  store contains info : " << nr[0]
                                    << " " << pol << " " << nr[1] << std::endl;
        // Store s (does not) contains t, since nr = (~)contains( s, t ) holds.
        d_extfInfoTmp[nr[0]].d_ctn[pol].push_back(nr[1]);
        d_extfInfoTmp[nr[0]].d_ctnFrom[pol].push_back(n);
        // Do transistive closure on contains, e.g.
        // if contains( s, t ) and ~contains( s, r ), then ~contains( t, r ).

        // The following infers new (negative) contains based on the above
        // reasoning, provided that ~contains( t, r ) does not
        // already hold in the current context. We test this by checking that
        // contains( t, r ) is not already asserted false in the current
        // context. We also handle the case where contains( t, r ) is equivalent
        // to t = r, in which case we check that t != r does not already hold
        // in the current context.

        // Notice that form of the above inference is enough to find
        // conflicts purely due to contains predicates. For example, if we
        // have only positive occurrences of contains, then no conflicts due to
        // contains predicates are possible and this schema does nothing. For
        // example, note that contains( s, t ) and contains( t, r ) implies
        // contains( s, r ), which we could but choose not to infer. Instead,
        // we prefer being lazy: only if ~contains( s, r ) appears later do we
        // infer ~contains( t, r ), which suffices to show a conflict.
        bool opol = !pol;
        for (unsigned i = 0, size = d_extfInfoTmp[nr[0]].d_ctn[opol].size();
             i < size;
             i++)
        {
          Node onr = d_extfInfoTmp[nr[0]].d_ctn[opol][i];
          Node concOrig =
              nm->mkNode(STRING_STRCTN, pol ? nr[1] : onr, pol ? onr : nr[1]);
          Node conc = Rewriter::rewrite(concOrig);
          // For termination concerns, we only do the inference if the contains
          // does not rewrite (and thus does not introduce new terms).
          if (conc == concOrig)
          {
            bool do_infer = false;
            conc = conc.negate();
            bool pol2 = conc.getKind() != NOT;
            Node lit = pol2 ? conc : conc[0];
            if (lit.getKind() == EQUAL)
            {
              do_infer = pol2 ? !d_state.areEqual(lit[0], lit[1])
                              : !d_state.areDisequal(lit[0], lit[1]);
            }
            else
            {
              do_infer = !d_state.areEqual(lit, pol2 ? d_true : d_false);
            }
            if (do_infer)
            {
              std::vector<Node> exp_c;
              exp_c.insert(exp_c.end(), in.d_exp.begin(), in.d_exp.end());
              Node ofrom = d_extfInfoTmp[nr[0]].d_ctnFrom[opol][i];
              Assert(d_extfInfoTmp.find(ofrom) != d_extfInfoTmp.end());
              exp_c.insert(exp_c.end(),
                           d_extfInfoTmp[ofrom].d_exp.begin(),
                           d_extfInfoTmp[ofrom].d_exp.end());
              d_im.sendInference(exp_c, conc, Inference::CTN_TRANS);
            }
          }
        }
      }
      else
      {
        // If we already know that s (does not) contain t, then n is redundant.
        // For example, if str.contains( x, y ), str.contains( z, y ), and x=z
        // are asserted in the current context, then str.contains( z, y ) is
        // satisfied by all models of str.contains( x, y ) ^ x=z and thus can
        // be ignored.
        Trace("strings-extf-debug") << "  redundant." << std::endl;
        d_extt.markReduced(n);
      }
    }
    return;
  }

  // If it's not a predicate, see if we can solve the equality n = c, where c
  // is the constant that extended term n is equal to.
  Node inferEq = nr.eqNode(in.d_const);
  Node inferEqr = Rewriter::rewrite(inferEq);
  Node inferEqrr = inferEqr;
  if (inferEqr.getKind() == EQUAL)
  {
    // try to use the extended rewriter for equalities
    inferEqrr = d_rewriter.rewriteEqualityExt(inferEqr);
  }
  if (inferEqrr != inferEqr)
  {
    inferEqrr = Rewriter::rewrite(inferEqrr);
    Trace("strings-extf-infer") << "checkExtfInference: " << inferEq
                                << " ...reduces to " << inferEqrr << std::endl;
    d_im.sendInternalInference(in.d_exp, inferEqrr, Inference::EXTF_EQ_REW);
  }
}

Node ExtfSolver::getCurrentSubstitutionFor(int effort,
                                           Node n,
                                           std::vector<Node>& exp)
{
  if (effort >= 3)
  {
    // model values
    Node mv = d_state.getModel()->getRepresentative(n);
    Trace("strings-subs") << "   model val : " << mv << std::endl;
    return mv;
  }
  Node nr = d_state.getRepresentative(n);
  Node c = d_bsolver.explainBestContentEqc(n, nr, exp);
  if (!c.isNull())
  {
    return c;
  }
  else if (effort >= 1 && n.getType().isStringLike())
  {
    Assert(effort < 3);
    // normal forms
    NormalForm& nfnr = d_csolver.getNormalForm(nr);
    Node ns = d_csolver.getNormalString(nfnr.d_base, exp);
    Trace("strings-subs") << "   normal eqc : " << ns << " " << nfnr.d_base
                          << " " << nr << std::endl;
    if (!nfnr.d_base.isNull())
    {
      d_im.addToExplanation(n, nfnr.d_base, exp);
    }
    return ns;
  }
  return n;
}

const std::map<Node, ExtfInfoTmp>& ExtfSolver::getInfo() const
{
  return d_extfInfoTmp;
}
bool ExtfSolver::hasExtendedFunctions() const { return d_hasExtf.get(); }

std::vector<Node> ExtfSolver::getActive(Kind k) const
{
  return d_extt.getActive(k);
}

bool StringsExtfCallback::getCurrentSubstitution(
    int effort,
    const std::vector<Node>& vars,
    std::vector<Node>& subs,
    std::map<Node, std::vector<Node> >& exp)
{
  Trace("strings-subs") << "getCurrentSubstitution, effort = " << effort
                        << std::endl;
  for (const Node& v : vars)
  {
    Trace("strings-subs") << "  get subs for " << v << "..." << std::endl;
    Node s = d_esolver->getCurrentSubstitutionFor(effort, v, exp[v]);
    subs.push_back(s);
  }
  return true;
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
