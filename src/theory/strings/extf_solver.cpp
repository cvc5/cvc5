/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of solver for extended functions of theory of strings.
 */

#include "theory/strings/extf_solver.h"

#include "options/strings_options.h"
#include "theory/strings/array_solver.h"
#include "theory/strings/sequences_rewriter.h"
#include "theory/strings/theory_strings_preprocess.h"
#include "theory/strings/theory_strings_utils.h"
#include "util/statistics_registry.h"

using namespace std;
using namespace cvc5::context;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

ExtfSolver::ExtfSolver(Env& env,
                       SolverState& s,
                       InferenceManager& im,
                       TermRegistry& tr,
                       StringsRewriter& rewriter,
                       BaseSolver& bs,
                       CoreSolver& cs,
                       ExtTheory& et,
                       SequencesStatistics& statistics)
    : EnvObj(env),
      d_state(s),
      d_im(im),
      d_termReg(tr),
      d_rewriter(rewriter),
      d_bsolver(bs),
      d_csolver(cs),
      d_extt(et),
      d_statistics(statistics),
      d_preproc(env, d_termReg.getSkolemCache(), &statistics.d_reductions),
      d_hasExtf(context(), false),
      d_extfInferCache(context()),
      d_reduced(userContext())
{
  d_extt.addFunctionKind(kind::STRING_SUBSTR);
  d_extt.addFunctionKind(kind::STRING_UPDATE);
  d_extt.addFunctionKind(kind::STRING_INDEXOF);
  d_extt.addFunctionKind(kind::STRING_INDEXOF_RE);
  d_extt.addFunctionKind(kind::STRING_ITOS);
  d_extt.addFunctionKind(kind::STRING_STOI);
  d_extt.addFunctionKind(kind::STRING_REPLACE);
  d_extt.addFunctionKind(kind::STRING_REPLACE_ALL);
  d_extt.addFunctionKind(kind::STRING_REPLACE_RE);
  d_extt.addFunctionKind(kind::STRING_REPLACE_RE_ALL);
  d_extt.addFunctionKind(kind::STRING_CONTAINS);
  d_extt.addFunctionKind(kind::STRING_IN_REGEXP);
  d_extt.addFunctionKind(kind::STRING_LEQ);
  d_extt.addFunctionKind(kind::STRING_TO_CODE);
  d_extt.addFunctionKind(kind::STRING_TO_LOWER);
  d_extt.addFunctionKind(kind::STRING_TO_UPPER);
  d_extt.addFunctionKind(kind::STRING_REV);
  d_extt.addFunctionKind(kind::STRING_UNIT);
  d_extt.addFunctionKind(kind::SEQ_UNIT);
  d_extt.addFunctionKind(kind::SEQ_NTH);

  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

ExtfSolver::~ExtfSolver() {}

bool ExtfSolver::shouldDoReduction(int effort, Node n, int pol)
{
  Trace("strings-extf-debug") << "shouldDoReduction " << n << ", pol " << pol
                              << ", effort " << effort << std::endl;
  if (!isActiveInModel(n))
  {
    // n is not active in the model, no need to reduce
    Trace("strings-extf-debug") << "...skip due to model active" << std::endl;
    return false;
  }
  // check with negation if requested (only applied to Boolean terms)
  Assert(n.getType().isBoolean() || pol != -1);
  Node nn = pol == -1 ? n.notNode() : n;
  if (d_reduced.find(nn) != d_reduced.end())
  {
    // already sent a reduction lemma
    Trace("strings-extf-debug") << "...skip due to reduced" << std::endl;
    return false;
  }
  Kind k = n.getKind();
  // determine if it is the right effort
  if (k == STRING_SUBSTR || (k == STRING_CONTAINS && pol == 1))
  {
    // we reduce these semi-eagerly, at effort 1
    return (effort == 1);
  }
  else if (k == STRING_CONTAINS && pol == -1)
  {
    // negative contains reduces at level 2, or 3 if guessing model
    int reffort = options().strings.stringModelBasedReduction ? 3 : 2;
    return (effort == reffort);
  }
  else if (k == SEQ_UNIT || k == STRING_UNIT || k == STRING_IN_REGEXP
           || k == STRING_TO_CODE || (n.getType().isBoolean() && pol == 0))
  {
    // never necessary to reduce seq.unit. str.to_code or str.in_re here.
    // also, we do not reduce str.contains that are preregistered but not
    // asserted (pol=0).
    return false;
  }
  else if (options().strings.seqArray != options::SeqArrayMode::NONE)
  {
    if (k == SEQ_NTH)
    {
      // don't need to reduce seq.nth when sequence update solver is used
      return false;
    }
    else if ((k == STRING_UPDATE || k == STRING_SUBSTR)
             && d_termReg.isHandledUpdateOrSubstr(n))
    {
      // don't need to reduce certain seq.update
      // don't need to reduce certain seq.extract with length 1
      return false;
    }
  }
  // all other operators reduce at level 2
  return (effort == 2);
}

void ExtfSolver::doReduction(Node n, int pol)
{
  Trace("strings-extf-debug")
      << "doReduction " << n << ", pol " << pol << std::endl;
  // polarity : 1 true, -1 false, 0 neither
  Kind k = n.getKind();
  if (k == STRING_CONTAINS && pol == -1)
  {
    Node x = n[0];
    Node s = n[1];
    std::vector<Node> lexp;
    Node lenx = d_state.getLength(x, lexp);
    Node lens = d_state.getLength(s, lexp);
    // we use an optimized reduction for negative string contains if the
    // lengths are equal
    if (d_state.areEqual(lenx, lens))
    {
      Trace("strings-extf-debug")
          << "  resolve extf : " << n << " based on equal lengths disequality."
          << std::endl;
      // We can reduce negative contains to a disequality when lengths are
      // equal. In other words, len( x ) = len( s ) implies
      //   ~contains( x, s ) reduces to x != s.
      // len( x ) = len( s ) ^ ~contains( x, s ) => x != s
      lexp.push_back(lenx.eqNode(lens));
      lexp.push_back(n.negate());
      Node xneqs = x.eqNode(s).negate();
      d_im.sendInference(
          lexp, xneqs, InferenceId::STRINGS_CTN_NEG_EQUAL, false, true);
      // this depends on the current assertions, so this
      // inference is context-dependent
      d_extt.markInactive(n, ExtReducedId::STRINGS_NEG_CTN_DEQ, true);
      return;
    }
  }
  Node nn = pol == -1 ? n.notNode() : n;
  Trace("strings-process-debug")
      << "Process reduction for " << n << ", pol = " << pol << std::endl;
  if (k == STRING_CONTAINS && pol == 1)
  {
    Node x = n[0];
    Node s = n[1];
    // positive contains reduces to a equality
    SkolemCache* skc = d_termReg.getSkolemCache();
    Node eq = d_termReg.eagerReduce(n, skc, d_termReg.getAlphabetCardinality());
    Assert(!eq.isNull());
    Assert(eq.getKind() == ITE && eq[0] == n);
    eq = eq[1];
    std::vector<Node> expn;
    expn.push_back(n);
    d_im.sendInference(expn, expn, eq, InferenceId::STRINGS_CTN_POS, false, true);
    Trace("strings-extf-debug")
        << "  resolve extf : " << n << " based on positive contain reduction."
        << std::endl;
    Trace("strings-red-lemma") << "Reduction (positive contains) lemma : " << n
                               << " => " << eq << std::endl;
    // reduced positively
    Assert(nn == n);
    d_reduced.insert(nn);
  }
  else
  {
    NodeManager* nm = NodeManager::currentNM();
    Assert(k == STRING_SUBSTR || k == STRING_UPDATE || k == STRING_CONTAINS
           || k == STRING_INDEXOF || k == STRING_INDEXOF_RE || k == STRING_ITOS
           || k == STRING_STOI || k == STRING_REPLACE || k == STRING_REPLACE_ALL
           || k == SEQ_NTH || k == STRING_REPLACE_RE
           || k == STRING_REPLACE_RE_ALL || k == STRING_LEQ
           || k == STRING_TO_LOWER || k == STRING_TO_UPPER || k == STRING_REV)
        << "Unknown reduction: " << k;
    std::vector<Node> new_nodes;
    Node res = d_preproc.simplify(n, new_nodes);
    Assert(res != n);
    new_nodes.push_back(n.eqNode(res));
    Node nnlem =
        new_nodes.size() == 1 ? new_nodes[0] : nm->mkNode(AND, new_nodes);
    // in rare case where it rewrites to true, just record it is reduced
    if (rewrite(nnlem) == d_true)
    {
      Trace("strings-extf-debug")
          << "  resolve extf : " << n << " based on (trivial) reduction."
          << std::endl;
      d_reduced.insert(nn);
    }
    else
    {
      InferInfo ii(InferenceId::STRINGS_REDUCTION);
      ii.d_conc = nnlem;
      d_im.sendInference(ii, true);
      Trace("strings-extf-debug")
          << "  resolve extf : " << n << " based on reduction." << std::endl;
      d_reduced.insert(nn);
    }
  }
}

void ExtfSolver::checkExtfReductionsEager()
{
  // return value is ignored
  checkExtfReductionsInternal(1, true);
}

void ExtfSolver::checkExtfReductions(Theory::Effort e)
{
  int effort = e == Theory::EFFORT_LAST_CALL ? 3 : 2;
  // return value is ignored
  checkExtfReductionsInternal(effort, true);
}

bool ExtfSolver::checkExtfReductionsInternal(int effort, bool doSend)
{
  // Notice we don't make a standard call to ExtTheory::doReductions here,
  // since certain optimizations like context-dependent reductions and
  // stratifying effort levels are done in doReduction below.
  // We only have to reduce extended functions that are both relevant and
  // active (see getRelevantActive).
  std::vector<Node> extf = getRelevantActive();
  Trace("strings-process") << "  checking " << extf.size() << " active extf"
                           << std::endl;
  for (const Node& n : extf)
  {
    Assert(!d_state.isInConflict());
    Trace("strings-extf-debug")
        << "  check " << n
        << ", active in model=" << d_extfInfoTmp[n].d_modelActive << std::endl;
    // polarity, 1: positive, -1: negative, 0: neither
    int pol = 0;
    if (n.getType().isBoolean())
    {
      Node rep = d_state.getRepresentative(n);
      if (rep.isConst())
      {
        pol = rep.getConst<bool>() ? 1 : -1;
      }
    }
    if (shouldDoReduction(effort, n, pol))
    {
      doReduction(n, pol);
      // we do not mark as inactive, since we may want to evaluate
      if (d_im.hasProcessed())
      {
        return true;
      }
    }
  }
  return false;
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
  std::unordered_set<Node> inferProcessed;
  for (const Node& n : terms)
  {
    // Setup information about n, including if it is equal to a constant.
    ExtfInfoTmp& einfo = d_extfInfoTmp[n];
    Assert(einfo.d_exp.empty());
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
    // seq.unit is parameterized
    if (n.getMetaKind() == metakind::PARAMETERIZED)
    {
      schildren.push_back(n.getOperator());
    }
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
          << ", constant = " << einfo.d_const << ", effort=" << effort
          << ", exp " << exp << std::endl;
      einfo.d_exp.insert(einfo.d_exp.end(), exp.begin(), exp.end());
      // inference is rewriting the substituted node
      Node nrc = rewrite(sn);
      // if rewrites to a constant, then do the inference and mark as reduced
      if (nrc.isConst())
      {
        // at effort=3, our substitution is from the model, and we don't do
        // inferences based on the model, instead we check whether the
        // cosntraint is already equal to its expected value below.
        if (effort < 3)
        {
          d_extt.markInactive(n, ExtReducedId::STRINGS_SR_CONST);
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
          if (options().strings.stringInferSym)
          {
            nrs = d_termReg.getSymbolicDefinition(sn, exps);
          }
          if (!nrs.isNull())
          {
            Trace("strings-extf-debug")
                << "  rewrite " << nrs << "..." << std::endl;
            Node nrsr = rewrite(nrs);
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
                conc = nrc == d_true ? n : n.negate();
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
            InferenceId inf = effort == 0 ? InferenceId::STRINGS_EXTF : InferenceId::STRINGS_EXTF_N;
            d_im.sendInference(einfo.d_exp, conc, inf, false, true);
            d_statistics.d_cdSimplifications << n.getKind();
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
      else if (effort < 3)
      {
        // if this was a predicate which changed after substitution + rewriting
        // We only do this before models are constructed (effort<3)
        if (!einfo.d_const.isNull() && nrc.getType().isBoolean() && nrc != n)
        {
          bool pol = einfo.d_const == d_true;
          Node nrcAssert = pol ? nrc : nrc.negate();
          Node nAssert = pol ? n : n.negate();
          einfo.d_exp.push_back(nAssert);
          Trace("strings-extf-debug") << "  decomposable..." << std::endl;
          Trace("strings-extf") << "  resolve extf : " << sn << " -> " << nrc
                                << ", const = " << einfo.d_const << std::endl;
          // We send inferences internal here, which may help show unsat.
          // However, we do not make a determination whether n can be marked
          // reduced since this argument may be circular: we may infer than n
          // can be reduced to something else, but that thing may argue that it
          // can be reduced to n, in theory.
          InferenceId infer =
              effort == 0 ? InferenceId::STRINGS_EXTF_D : InferenceId::STRINGS_EXTF_D_N;
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
      if (effort == 1)
      {
        Trace("strings-extf")
            << "  cannot rewrite extf : " << to_reduce << std::endl;
      }
      // we take to_reduce to be the (partially) reduced version of n, which
      // is justified by the explanation in einfo. We only do this if we are
      // not based on the model (effort<3).
      if (effort < 3)
      {
        checkExtfInference(n, to_reduce, einfo, effort);
      }
      if (TraceIsOn("strings-extf-list"))
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
    if (d_state.isInConflict())
    {
      Trace("strings-extf-debug") << "  conflict, return." << std::endl;
      return;
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
  Trace("strings-extf-infer")
      << "checkExtfInference: " << n << " : " << nr << " == " << in.d_const
      << " with exp " << in.d_exp << std::endl;

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

  if (nr.getKind() == STRING_CONTAINS)
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
          Node conc = nm->mkNode(STRING_CONTAINS, children);
          conc = rewrite(pol ? conc : conc.negate());
          // check if it already (does not) hold
          if (d_state.hasTerm(conc))
          {
            if (d_state.areEqual(conc, d_false))
            {
              // we are in conflict
              d_im.addToExplanation(conc, d_false, in.d_exp);
              d_im.sendInference(
                  in.d_exp, d_false, InferenceId::STRINGS_CTN_DECOMPOSE);
              Assert(d_state.isInConflict());
              return;
            }
            else if (d_extt.hasFunctionKind(conc.getKind()))
            {
              // can mark as reduced, since model for n implies model for conc
              d_extt.markInactive(conc, ExtReducedId::STRINGS_CTN_DECOMPOSE);
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
              nm->mkNode(STRING_CONTAINS, pol ? nr[1] : onr, pol ? onr : nr[1]);
          Node conc = rewrite(concOrig);
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
              d_im.sendInference(exp_c, conc, InferenceId::STRINGS_CTN_TRANS);
            }
          }
        }
      }
      else
      {
        // If we already know that s (does not) contain t, then n may be
        // redundant. However, we do not mark n as reduced here, since strings
        // reductions may require dependencies between extended functions.
        // Marking reduced here could lead to incorrect models if an
        // extended function is marked reduced based on an assignment to
        // something that depends on n.
        Trace("strings-extf-debug") << "  redundant." << std::endl;
      }
    }
    return;
  }

  // If it's not a predicate, see if we can solve the equality n = c, where c
  // is the constant that extended term n is equal to.
  Node inferEq = nr.eqNode(in.d_const);
  Node inferEqr = rewrite(inferEq);
  Node inferEqrr = inferEqr;
  if (inferEqr.getKind() == EQUAL)
  {
    // try to use the extended rewriter for equalities
    inferEqrr = d_rewriter.rewriteEqualityExt(inferEqr);
  }
  if (inferEqrr != inferEqr)
  {
    inferEqrr = rewrite(inferEqrr);
    Trace("strings-extf-infer")
        << "checkExtfInference: " << inferEq << " ...reduces to " << inferEqrr
        << " with explanation " << in.d_exp << std::endl;
    d_im.sendInternalInference(in.d_exp, inferEqrr, InferenceId::STRINGS_EXTF_EQ_REW);
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
  // if the normal form is available, use it
  if (effort >= 1 && n.getType().isStringLike())
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
  // otherwise, we use the best content heuristic
  Node c = d_bsolver.explainBestContentEqc(n, nr, exp);
  if (!c.isNull())
  {
    return c;
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

bool ExtfSolver::isActiveInModel(Node n) const
{
  std::map<Node, ExtfInfoTmp>::const_iterator it = d_extfInfoTmp.find(n);
  if (it == d_extfInfoTmp.end())
  {
    Assert(false) << "isActiveInModel: Expected extf info for " << n;
    return true;
  }
  return it->second.d_modelActive;
}

std::vector<Node> ExtfSolver::getRelevantActive() const
{
  // get the relevant term set
  std::vector<Node> extf = d_extt.getActive();
  const std::set<Node>& relevantTerms = d_termReg.getRelevantTermSet();

  std::vector<Node> res;
  for (const Node& n : extf)
  {
    if (relevantTerms.find(n) == relevantTerms.end())
    {
      // not relevant
      continue;
    }
    res.push_back(n);
  }
  return res;
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

std::string ExtfSolver::debugPrintModel()
{
  std::stringstream ss;
  std::vector<Node> extf;
  d_extt.getTerms(extf);
  // each extended function should have at least one annotation below
  for (const Node& n : extf)
  {
    ss << "- " << n;
    ExtReducedId id;
    if (!d_extt.isActive(n, id))
    {
      ss << " :extt-inactive " << id;
    }
    if (!d_extfInfoTmp[n].d_modelActive)
    {
      ss << " :model-inactive";
    }
    if (d_reduced.find(n) != d_reduced.end())
    {
      ss << " :reduced";
    }
    ss << std::endl;
  }
  return ss.str();
}

bool ExtfSolver::isReduced(const Node& n) const
{
  return d_reduced.find(n) != d_reduced.end();
}

void ExtfSolver::markReduced(const Node& n) { d_reduced.insert(n); }

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
