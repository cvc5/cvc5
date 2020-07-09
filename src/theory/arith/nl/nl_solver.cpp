/*********************                                                        */
/*! \file nl_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Ahmed Irfan
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of non-linear solver
 **/

#include "theory/arith/nl/nl_solver.h"

#include "options/arith_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/theory_arith.h"
#include "theory/theory_model.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

void debugPrintBound(const char* c, Node coeff, Node x, Kind type, Node rhs)
{
  Node t = ArithMSum::mkCoeffTerm(coeff, x);
  Trace(c) << t << " " << type << " " << rhs;
}

bool hasNewMonomials(Node n, const std::vector<Node>& existing)
{
  std::set<Node> visited;

  std::vector<Node> worklist;
  worklist.push_back(n);
  while (!worklist.empty())
  {
    Node current = worklist.back();
    worklist.pop_back();
    if (visited.find(current) == visited.end())
    {
      visited.insert(current);
      if (current.getKind() == NONLINEAR_MULT)
      {
        if (std::find(existing.begin(), existing.end(), current)
            == existing.end())
        {
          return true;
        }
      }
      else
      {
        worklist.insert(worklist.end(), current.begin(), current.end());
      }
    }
  }
  return false;
}

NlSolver::NlSolver(TheoryArith& containing, NlModel& model)
    : d_containing(containing),
      d_model(model),
      d_cdb(d_mdb),
      d_zero_split(containing.getUserContext())
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
  d_zero = nm->mkConst(Rational(0));
  d_one = nm->mkConst(Rational(1));
  d_neg_one = nm->mkConst(Rational(-1));
  d_order_points.push_back(d_neg_one);
  d_order_points.push_back(d_zero);
  d_order_points.push_back(d_one);
}

NlSolver::~NlSolver() {}

void NlSolver::initLastCall(const std::vector<Node>& assertions,
                            const std::vector<Node>& false_asserts,
                            const std::vector<Node>& xts)
{
  d_ms_vars.clear();
  d_ms_proc.clear();
  d_ms.clear();
  d_mterms.clear();
  d_m_nconst_factor.clear();
  d_tplane_refine.clear();
  d_ci.clear();
  d_ci_exp.clear();
  d_ci_max.clear();

  Trace("nl-ext-mv") << "Extended terms : " << std::endl;
  // for computing congruence
  std::map<Kind, ArgTrie> argTrie;
  for (unsigned i = 0, xsize = xts.size(); i < xsize; i++)
  {
    Node a = xts[i];
    d_model.computeConcreteModelValue(a);
    d_model.computeAbstractModelValue(a);
    d_model.printModelValue("nl-ext-mv", a);
    Kind ak = a.getKind();
    if (ak == NONLINEAR_MULT)
    {
      d_ms.push_back(a);

      // context-independent registration
      d_mdb.registerMonomial(a);

      const std::vector<Node>& varList = d_mdb.getVariableList(a);
      for (const Node& v : varList)
      {
        if (std::find(d_ms_vars.begin(), d_ms_vars.end(), v) == d_ms_vars.end())
        {
          d_ms_vars.push_back(v);
        }
        Node mvk = d_model.computeAbstractModelValue(v);
        if (!mvk.isConst())
        {
          d_m_nconst_factor[a] = true;
        }
      }
      // mark processed if has a "one" factor (will look at reduced monomial)?
    }
  }

  // register constants
  d_mdb.registerMonomial(d_one);
  for (unsigned j = 0; j < d_order_points.size(); j++)
  {
    Node c = d_order_points[j];
    d_model.computeConcreteModelValue(c);
    d_model.computeAbstractModelValue(c);
  }

  // register variables
  Trace("nl-ext-mv") << "Variables in monomials : " << std::endl;
  for (unsigned i = 0; i < d_ms_vars.size(); i++)
  {
    Node v = d_ms_vars[i];
    d_mdb.registerMonomial(v);
    d_model.computeConcreteModelValue(v);
    d_model.computeAbstractModelValue(v);
    d_model.printModelValue("nl-ext-mv", v);
  }

  Trace("nl-ext") << "We have " << d_ms.size() << " monomials." << std::endl;
}

void NlSolver::setMonomialFactor(Node a, Node b, const NodeMultiset& common)
{
  // Could not tell if this was being inserted intentionally or not.
  std::map<Node, Node>& mono_diff_a = d_mono_diff[a];
  if (mono_diff_a.find(b) == mono_diff_a.end())
  {
    Trace("nl-ext-mono-factor")
        << "Set monomial factor for " << a << "/" << b << std::endl;
    mono_diff_a[b] = d_mdb.mkMonomialRemFactor(a, common);
  }
}

std::vector<NlLemma> NlSolver::checkSplitZero()
{
  std::vector<NlLemma> lemmas;
  for (unsigned i = 0; i < d_ms_vars.size(); i++)
  {
    Node v = d_ms_vars[i];
    if (d_zero_split.insert(v))
    {
      Node eq = v.eqNode(d_zero);
      eq = Rewriter::rewrite(eq);
      Node literal = d_containing.getValuation().ensureLiteral(eq);
      d_containing.getOutputChannel().requirePhase(literal, true);
      lemmas.emplace_back(literal.orNode(literal.negate()),
                          Inference::SPLIT_ZERO);
    }
  }
  return lemmas;
}

void NlSolver::assignOrderIds(std::vector<Node>& vars,
                              NodeMultiset& order,
                              bool isConcrete,
                              bool isAbsolute)
{
  SortNlModel smv;
  smv.d_nlm = &d_model;
  smv.d_isConcrete = isConcrete;
  smv.d_isAbsolute = isAbsolute;
  smv.d_reverse_order = false;
  std::sort(vars.begin(), vars.end(), smv);

  order.clear();
  // assign ordering id's
  unsigned counter = 0;
  unsigned order_index = isConcrete ? 0 : 1;
  Node prev;
  for (unsigned j = 0; j < vars.size(); j++)
  {
    Node x = vars[j];
    Node v = d_model.computeModelValue(x, isConcrete);
    if (!v.isConst())
    {
      Trace("nl-ext-mvo") << "..do not assign order to " << x << " : " << v
                          << std::endl;
      // don't assign for non-constant values (transcendental function apps)
      break;
    }
    Trace("nl-ext-mvo") << "  order " << x << " : " << v << std::endl;
    if (v != prev)
    {
      // builtin points
      bool success;
      do
      {
        success = false;
        if (order_index < d_order_points.size())
        {
          Node vv = d_model.computeModelValue(d_order_points[order_index],
                                              isConcrete);
          if (d_model.compareValue(v, vv, isAbsolute) <= 0)
          {
            counter++;
            Trace("nl-ext-mvo") << "O[" << d_order_points[order_index]
                                << "] = " << counter << std::endl;
            order[d_order_points[order_index]] = counter;
            prev = vv;
            order_index++;
            success = true;
          }
        }
      } while (success);
    }
    if (prev.isNull() || d_model.compareValue(v, prev, isAbsolute) != 0)
    {
      counter++;
    }
    Trace("nl-ext-mvo") << "O[" << x << "] = " << counter << std::endl;
    order[x] = counter;
    prev = v;
  }
  while (order_index < d_order_points.size())
  {
    counter++;
    Trace("nl-ext-mvo") << "O[" << d_order_points[order_index]
                        << "] = " << counter << std::endl;
    order[d_order_points[order_index]] = counter;
    order_index++;
  }
}

// show a <> 0 by inequalities between variables in monomial a w.r.t 0
int NlSolver::compareSign(Node oa,
                          Node a,
                          unsigned a_index,
                          int status,
                          std::vector<Node>& exp,
                          std::vector<NlLemma>& lem)
{
  Trace("nl-ext-debug") << "Process " << a << " at index " << a_index
                        << ", status is " << status << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  Node mvaoa = d_model.computeAbstractModelValue(oa);
  const std::vector<Node>& vla = d_mdb.getVariableList(a);
  if (a_index == vla.size())
  {
    if (mvaoa.getConst<Rational>().sgn() != status)
    {
      Node lemma =
          safeConstructNary(AND, exp).impNode(mkLit(oa, d_zero, status * 2));
      lem.emplace_back(lemma, Inference::SIGN);
    }
    return status;
  }
  Assert(a_index < vla.size());
  Node av = vla[a_index];
  unsigned aexp = d_mdb.getExponent(a, av);
  // take current sign in model
  Node mvaav = d_model.computeAbstractModelValue(av);
  int sgn = mvaav.getConst<Rational>().sgn();
  Trace("nl-ext-debug") << "Process var " << av << "^" << aexp
                        << ", model sign = " << sgn << std::endl;
  if (sgn == 0)
  {
    if (mvaoa.getConst<Rational>().sgn() != 0)
    {
      Node lemma = av.eqNode(d_zero).impNode(oa.eqNode(d_zero));
      lem.emplace_back(lemma, Inference::SIGN);
    }
    return 0;
  }
  if (aexp % 2 == 0)
  {
    exp.push_back(av.eqNode(d_zero).negate());
    return compareSign(oa, a, a_index + 1, status, exp, lem);
  }
  exp.push_back(nm->mkNode(sgn == 1 ? GT : LT, av, d_zero));
  return compareSign(oa, a, a_index + 1, status * sgn, exp, lem);
}

bool NlSolver::compareMonomial(
    Node oa,
    Node a,
    NodeMultiset& a_exp_proc,
    Node ob,
    Node b,
    NodeMultiset& b_exp_proc,
    std::vector<Node>& exp,
    std::vector<NlLemma>& lem,
    std::map<int, std::map<Node, std::map<Node, Node> > >& cmp_infers)
{
  Trace("nl-ext-comp-debug")
      << "Check |" << a << "| >= |" << b << "|" << std::endl;
  unsigned pexp_size = exp.size();
  if (compareMonomial(
          oa, a, 0, a_exp_proc, ob, b, 0, b_exp_proc, 0, exp, lem, cmp_infers))
  {
    return true;
  }
  exp.resize(pexp_size);
  Trace("nl-ext-comp-debug")
      << "Check |" << b << "| >= |" << a << "|" << std::endl;
  if (compareMonomial(
          ob, b, 0, b_exp_proc, oa, a, 0, a_exp_proc, 0, exp, lem, cmp_infers))
  {
    return true;
  }
  return false;
}

Node NlSolver::mkLit(Node a, Node b, int status, bool isAbsolute)
{
  if (status == 0)
  {
    Node a_eq_b = a.eqNode(b);
    if (!isAbsolute)
    {
      return a_eq_b;
    }
    Node negate_b = NodeManager::currentNM()->mkNode(UMINUS, b);
    return a_eq_b.orNode(a.eqNode(negate_b));
  }
  else if (status < 0)
  {
    return mkLit(b, a, -status);
  }
  Assert(status == 1 || status == 2);
  NodeManager* nm = NodeManager::currentNM();
  Kind greater_op = status == 1 ? GEQ : GT;
  if (!isAbsolute)
  {
    return nm->mkNode(greater_op, a, b);
  }
  // return nm->mkNode( greater_op, mkAbs( a ), mkAbs( b ) );
  Node zero = mkRationalNode(0);
  Node a_is_nonnegative = nm->mkNode(GEQ, a, zero);
  Node b_is_nonnegative = nm->mkNode(GEQ, b, zero);
  Node negate_a = nm->mkNode(UMINUS, a);
  Node negate_b = nm->mkNode(UMINUS, b);
  return a_is_nonnegative.iteNode(
      b_is_nonnegative.iteNode(nm->mkNode(greater_op, a, b),
                               nm->mkNode(greater_op, a, negate_b)),
      b_is_nonnegative.iteNode(nm->mkNode(greater_op, negate_a, b),
                               nm->mkNode(greater_op, negate_a, negate_b)));
}

bool NlSolver::cmp_holds(Node x,
                         Node y,
                         std::map<Node, std::map<Node, Node> >& cmp_infers,
                         std::vector<Node>& exp,
                         std::map<Node, bool>& visited)
{
  if (x == y)
  {
    return true;
  }
  else if (visited.find(x) != visited.end())
  {
    return false;
  }
  visited[x] = true;
  std::map<Node, std::map<Node, Node> >::iterator it = cmp_infers.find(x);
  if (it != cmp_infers.end())
  {
    for (std::map<Node, Node>::iterator itc = it->second.begin();
         itc != it->second.end();
         ++itc)
    {
      exp.push_back(itc->second);
      if (cmp_holds(itc->first, y, cmp_infers, exp, visited))
      {
        return true;
      }
      exp.pop_back();
    }
  }
  return false;
}

// trying to show a ( >, = ) b   by inequalities between variables in
// monomials a,b
bool NlSolver::compareMonomial(
    Node oa,
    Node a,
    unsigned a_index,
    NodeMultiset& a_exp_proc,
    Node ob,
    Node b,
    unsigned b_index,
    NodeMultiset& b_exp_proc,
    int status,
    std::vector<Node>& exp,
    std::vector<NlLemma>& lem,
    std::map<int, std::map<Node, std::map<Node, Node> > >& cmp_infers)
{
  Trace("nl-ext-comp-debug")
      << "compareMonomial " << oa << " and " << ob << ", indices = " << a_index
      << " " << b_index << std::endl;
  Assert(status == 0 || status == 2);
  const std::vector<Node>& vla = d_mdb.getVariableList(a);
  const std::vector<Node>& vlb = d_mdb.getVariableList(b);
  if (a_index == vla.size() && b_index == vlb.size())
  {
    // finished, compare absolute value of abstract model values
    int modelStatus = d_model.compare(oa, ob, false, true) * -2;
    Trace("nl-ext-comp") << "...finished comparison with " << oa << " <"
                         << status << "> " << ob
                         << ", model status = " << modelStatus << std::endl;
    if (status != modelStatus)
    {
      Trace("nl-ext-comp-infer")
          << "infer : " << oa << " <" << status << "> " << ob << std::endl;
      if (status == 2)
      {
        // must state that all variables are non-zero
        for (unsigned j = 0; j < vla.size(); j++)
        {
          exp.push_back(vla[j].eqNode(d_zero).negate());
        }
      }
      NodeManager* nm = NodeManager::currentNM();
      Node clem = nm->mkNode(
          IMPLIES, safeConstructNary(AND, exp), mkLit(oa, ob, status, true));
      Trace("nl-ext-comp-lemma") << "comparison lemma : " << clem << std::endl;
      lem.emplace_back(clem, Inference::COMPARISON);
      cmp_infers[status][oa][ob] = clem;
    }
    return true;
  }
  // get a/b variable information
  Node av;
  unsigned aexp = 0;
  unsigned avo = 0;
  if (a_index < vla.size())
  {
    av = vla[a_index];
    unsigned aexpTotal = d_mdb.getExponent(a, av);
    Assert(a_exp_proc[av] <= aexpTotal);
    aexp = aexpTotal - a_exp_proc[av];
    if (aexp == 0)
    {
      return compareMonomial(oa,
                             a,
                             a_index + 1,
                             a_exp_proc,
                             ob,
                             b,
                             b_index,
                             b_exp_proc,
                             status,
                             exp,
                             lem,
                             cmp_infers);
    }
    Assert(d_order_vars.find(av) != d_order_vars.end());
    avo = d_order_vars[av];
  }
  Node bv;
  unsigned bexp = 0;
  unsigned bvo = 0;
  if (b_index < vlb.size())
  {
    bv = vlb[b_index];
    unsigned bexpTotal = d_mdb.getExponent(b, bv);
    Assert(b_exp_proc[bv] <= bexpTotal);
    bexp = bexpTotal - b_exp_proc[bv];
    if (bexp == 0)
    {
      return compareMonomial(oa,
                             a,
                             a_index,
                             a_exp_proc,
                             ob,
                             b,
                             b_index + 1,
                             b_exp_proc,
                             status,
                             exp,
                             lem,
                             cmp_infers);
    }
    Assert(d_order_vars.find(bv) != d_order_vars.end());
    bvo = d_order_vars[bv];
  }
  // get "one" information
  Assert(d_order_vars.find(d_one) != d_order_vars.end());
  unsigned ovo = d_order_vars[d_one];
  Trace("nl-ext-comp-debug") << "....vars : " << av << "^" << aexp << " " << bv
                             << "^" << bexp << std::endl;

  //--- cases
  if (av.isNull())
  {
    if (bvo <= ovo)
    {
      Trace("nl-ext-comp-debug") << "...take leading " << bv << std::endl;
      // can multiply b by <=1
      exp.push_back(mkLit(d_one, bv, bvo == ovo ? 0 : 2, true));
      return compareMonomial(oa,
                             a,
                             a_index,
                             a_exp_proc,
                             ob,
                             b,
                             b_index + 1,
                             b_exp_proc,
                             bvo == ovo ? status : 2,
                             exp,
                             lem,
                             cmp_infers);
    }
    Trace("nl-ext-comp-debug")
        << "...failure, unmatched |b|>1 component." << std::endl;
    return false;
  }
  else if (bv.isNull())
  {
    if (avo >= ovo)
    {
      Trace("nl-ext-comp-debug") << "...take leading " << av << std::endl;
      // can multiply a by >=1
      exp.push_back(mkLit(av, d_one, avo == ovo ? 0 : 2, true));
      return compareMonomial(oa,
                             a,
                             a_index + 1,
                             a_exp_proc,
                             ob,
                             b,
                             b_index,
                             b_exp_proc,
                             avo == ovo ? status : 2,
                             exp,
                             lem,
                             cmp_infers);
    }
    Trace("nl-ext-comp-debug")
        << "...failure, unmatched |a|<1 component." << std::endl;
    return false;
  }
  Assert(!av.isNull() && !bv.isNull());
  if (avo >= bvo)
  {
    if (bvo < ovo && avo >= ovo)
    {
      Trace("nl-ext-comp-debug") << "...take leading " << av << std::endl;
      // do avo>=1 instead
      exp.push_back(mkLit(av, d_one, avo == ovo ? 0 : 2, true));
      return compareMonomial(oa,
                             a,
                             a_index + 1,
                             a_exp_proc,
                             ob,
                             b,
                             b_index,
                             b_exp_proc,
                             avo == ovo ? status : 2,
                             exp,
                             lem,
                             cmp_infers);
    }
    unsigned min_exp = aexp > bexp ? bexp : aexp;
    a_exp_proc[av] += min_exp;
    b_exp_proc[bv] += min_exp;
    Trace("nl-ext-comp-debug") << "...take leading " << min_exp << " from "
                               << av << " and " << bv << std::endl;
    exp.push_back(mkLit(av, bv, avo == bvo ? 0 : 2, true));
    bool ret = compareMonomial(oa,
                               a,
                               a_index,
                               a_exp_proc,
                               ob,
                               b,
                               b_index,
                               b_exp_proc,
                               avo == bvo ? status : 2,
                               exp,
                               lem,
                               cmp_infers);
    a_exp_proc[av] -= min_exp;
    b_exp_proc[bv] -= min_exp;
    return ret;
  }
  if (bvo <= ovo)
  {
    Trace("nl-ext-comp-debug") << "...take leading " << bv << std::endl;
    // try multiply b <= 1
    exp.push_back(mkLit(d_one, bv, bvo == ovo ? 0 : 2, true));
    return compareMonomial(oa,
                           a,
                           a_index,
                           a_exp_proc,
                           ob,
                           b,
                           b_index + 1,
                           b_exp_proc,
                           bvo == ovo ? status : 2,
                           exp,
                           lem,
                           cmp_infers);
  }
  Trace("nl-ext-comp-debug")
      << "...failure, leading |b|>|a|>1 component." << std::endl;
  return false;
}

std::vector<NlLemma> NlSolver::checkMonomialSign()
{
  std::vector<NlLemma> lemmas;
  std::map<Node, int> signs;
  Trace("nl-ext") << "Get monomial sign lemmas..." << std::endl;
  for (unsigned j = 0; j < d_ms.size(); j++)
  {
    Node a = d_ms[j];
    if (d_ms_proc.find(a) == d_ms_proc.end())
    {
      std::vector<Node> exp;
      if (Trace.isOn("nl-ext-debug"))
      {
        Node cmva = d_model.computeConcreteModelValue(a);
        Trace("nl-ext-debug")
            << "  process " << a << ", mv=" << cmva << "..." << std::endl;
      }
      if (d_m_nconst_factor.find(a) == d_m_nconst_factor.end())
      {
        signs[a] = compareSign(a, a, 0, 1, exp, lemmas);
        if (signs[a] == 0)
        {
          d_ms_proc[a] = true;
          Trace("nl-ext-debug")
              << "...mark " << a << " reduced since its value is 0."
              << std::endl;
        }
      }
      else
      {
        Trace("nl-ext-debug")
            << "...can't conclude sign lemma for " << a
            << " since model value of a factor is non-constant." << std::endl;
      }
    }
  }
  return lemmas;
}

std::vector<NlLemma> NlSolver::checkMonomialMagnitude(unsigned c)
{
  // ensure information is setup
  if (c == 0)
  {
    // sort by absolute values of abstract model values
    assignOrderIds(d_ms_vars, d_order_vars, false, true);

    // sort individual variable lists
    Trace("nl-ext-proc") << "Assign order var lists..." << std::endl;
    d_mdb.sortVariablesByModel(d_ms, d_model);
  }

  unsigned r = 1;
  std::vector<NlLemma> lemmas;
  // if (x,y,L) in cmp_infers, then x > y inferred as conclusion of L
  // in lemmas
  std::map<int, std::map<Node, std::map<Node, Node> > > cmp_infers;
  Trace("nl-ext") << "Get monomial comparison lemmas (order=" << r
                  << ", compare=" << c << ")..." << std::endl;
  for (unsigned j = 0; j < d_ms.size(); j++)
  {
    Node a = d_ms[j];
    if (d_ms_proc.find(a) == d_ms_proc.end()
        && d_m_nconst_factor.find(a) == d_m_nconst_factor.end())
    {
      if (c == 0)
      {
        // compare magnitude against 1
        std::vector<Node> exp;
        NodeMultiset a_exp_proc;
        NodeMultiset b_exp_proc;
        compareMonomial(a,
                        a,
                        a_exp_proc,
                        d_one,
                        d_one,
                        b_exp_proc,
                        exp,
                        lemmas,
                        cmp_infers);
      }
      else
      {
        const NodeMultiset& mea = d_mdb.getMonomialExponentMap(a);
        if (c == 1)
        {
          // could compare not just against containing variables?
          // compare magnitude against variables
          for (unsigned k = 0; k < d_ms_vars.size(); k++)
          {
            Node v = d_ms_vars[k];
            Node mvcv = d_model.computeConcreteModelValue(v);
            if (mvcv.isConst())
            {
              std::vector<Node> exp;
              NodeMultiset a_exp_proc;
              NodeMultiset b_exp_proc;
              if (mea.find(v) != mea.end())
              {
                a_exp_proc[v] = 1;
                b_exp_proc[v] = 1;
                setMonomialFactor(a, v, a_exp_proc);
                setMonomialFactor(v, a, b_exp_proc);
                compareMonomial(a,
                                a,
                                a_exp_proc,
                                v,
                                v,
                                b_exp_proc,
                                exp,
                                lemmas,
                                cmp_infers);
              }
            }
          }
        }
        else
        {
          // compare magnitude against other non-linear monomials
          for (unsigned k = (j + 1); k < d_ms.size(); k++)
          {
            Node b = d_ms[k];
            //(signs[a]==signs[b])==(r==0)
            if (d_ms_proc.find(b) == d_ms_proc.end()
                && d_m_nconst_factor.find(b) == d_m_nconst_factor.end())
            {
              const NodeMultiset& meb = d_mdb.getMonomialExponentMap(b);

              std::vector<Node> exp;
              // take common factors of monomials, set minimum of
              // common exponents as processed
              NodeMultiset a_exp_proc;
              NodeMultiset b_exp_proc;
              for (NodeMultiset::const_iterator itmea2 = mea.begin();
                   itmea2 != mea.end();
                   ++itmea2)
              {
                NodeMultiset::const_iterator itmeb2 = meb.find(itmea2->first);
                if (itmeb2 != meb.end())
                {
                  unsigned min_exp = itmea2->second > itmeb2->second
                                         ? itmeb2->second
                                         : itmea2->second;
                  a_exp_proc[itmea2->first] = min_exp;
                  b_exp_proc[itmea2->first] = min_exp;
                  Trace("nl-ext-comp") << "Common exponent : " << itmea2->first
                                       << " : " << min_exp << std::endl;
                }
              }
              if (!a_exp_proc.empty())
              {
                setMonomialFactor(a, b, a_exp_proc);
                setMonomialFactor(b, a, b_exp_proc);
              }
              /*
              if( !a_exp_proc.empty() ){
                //reduction based on common exponents a > 0 => ( a * b
              <> a * c <=> b <> c ), a < 0 => ( a * b <> a * c <=> b
              !<> c )  ? }else{ compareMonomial( a, a, a_exp_proc, b,
              b, b_exp_proc, exp, lemmas );
              }
              */
              compareMonomial(
                  a, a, a_exp_proc, b, b, b_exp_proc, exp, lemmas, cmp_infers);
            }
          }
        }
      }
    }
  }
  // remove redundant lemmas, e.g. if a > b, b > c, a > c were
  // inferred, discard lemma with conclusion a > c
  Trace("nl-ext-comp") << "Compute redundancies for " << lemmas.size()
                       << " lemmas." << std::endl;
  // naive
  std::unordered_set<Node, NodeHashFunction> r_lemmas;
  for (std::map<int, std::map<Node, std::map<Node, Node> > >::iterator itb =
           cmp_infers.begin();
       itb != cmp_infers.end();
       ++itb)
  {
    for (std::map<Node, std::map<Node, Node> >::iterator itc =
             itb->second.begin();
         itc != itb->second.end();
         ++itc)
    {
      for (std::map<Node, Node>::iterator itc2 = itc->second.begin();
           itc2 != itc->second.end();
           ++itc2)
      {
        std::map<Node, bool> visited;
        for (std::map<Node, Node>::iterator itc3 = itc->second.begin();
             itc3 != itc->second.end();
             ++itc3)
        {
          if (itc3->first != itc2->first)
          {
            std::vector<Node> exp;
            if (cmp_holds(itc3->first, itc2->first, itb->second, exp, visited))
            {
              r_lemmas.insert(itc2->second);
              Trace("nl-ext-comp")
                  << "...inference of " << itc->first << " > " << itc2->first
                  << " was redundant." << std::endl;
              break;
            }
          }
        }
      }
    }
  }
  std::vector<NlLemma> nr_lemmas;
  for (unsigned i = 0; i < lemmas.size(); i++)
  {
    if (r_lemmas.find(lemmas[i].d_lemma) == r_lemmas.end())
    {
      nr_lemmas.push_back(lemmas[i]);
    }
  }
  // could only take maximal lower/minimial lower bounds?

  Trace("nl-ext-comp") << nr_lemmas.size() << " / " << lemmas.size()
                       << " were non-redundant." << std::endl;
  return nr_lemmas;
}

std::vector<NlLemma> NlSolver::checkTangentPlanes()
{
  std::vector<NlLemma> lemmas;
  Trace("nl-ext") << "Get monomial tangent plane lemmas..." << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  const std::map<Node, std::vector<Node> >& ccMap =
      d_mdb.getContainsChildrenMap();
  unsigned kstart = d_ms_vars.size();
  for (unsigned k = kstart; k < d_mterms.size(); k++)
  {
    Node t = d_mterms[k];
    // if this term requires a refinement
    if (d_tplane_refine.find(t) == d_tplane_refine.end())
    {
      continue;
    }
    Trace("nl-ext-tplanes")
        << "Look at monomial requiring refinement : " << t << std::endl;
    // get a decomposition
    std::map<Node, std::vector<Node> >::const_iterator it = ccMap.find(t);
    if (it == ccMap.end())
    {
      continue;
    }
    std::map<Node, std::map<Node, bool> > dproc;
    for (unsigned j = 0; j < it->second.size(); j++)
    {
      Node tc = it->second[j];
      if (tc != d_one)
      {
        Node tc_diff = d_mdb.getContainsDiffNl(tc, t);
        Assert(!tc_diff.isNull());
        Node a = tc < tc_diff ? tc : tc_diff;
        Node b = tc < tc_diff ? tc_diff : tc;
        if (dproc[a].find(b) == dproc[a].end())
        {
          dproc[a][b] = true;
          Trace("nl-ext-tplanes")
              << "  decomposable into : " << a << " * " << b << std::endl;
          Node a_v_c = d_model.computeAbstractModelValue(a);
          Node b_v_c = d_model.computeAbstractModelValue(b);
          // points we will add tangent planes for
          std::vector<Node> pts[2];
          pts[0].push_back(a_v_c);
          pts[1].push_back(b_v_c);
          // if previously refined
          bool prevRefine = d_tangent_val_bound[0][a].find(b)
                            != d_tangent_val_bound[0][a].end();
          // a_min, a_max, b_min, b_max
          for (unsigned p = 0; p < 4; p++)
          {
            Node curr_v = p <= 1 ? a_v_c : b_v_c;
            if (prevRefine)
            {
              Node pt_v = d_tangent_val_bound[p][a][b];
              Assert(!pt_v.isNull());
              if (curr_v != pt_v)
              {
                Node do_extend =
                    nm->mkNode((p == 1 || p == 3) ? GT : LT, curr_v, pt_v);
                do_extend = Rewriter::rewrite(do_extend);
                if (do_extend == d_true)
                {
                  for (unsigned q = 0; q < 2; q++)
                  {
                    pts[p <= 1 ? 0 : 1].push_back(curr_v);
                    pts[p <= 1 ? 1 : 0].push_back(
                        d_tangent_val_bound[p <= 1 ? 2 + q : q][a][b]);
                  }
                }
              }
            }
            else
            {
              d_tangent_val_bound[p][a][b] = curr_v;
            }
          }

          for (unsigned p = 0; p < pts[0].size(); p++)
          {
            Node a_v = pts[0][p];
            Node b_v = pts[1][p];

            // tangent plane
            Node tplane = nm->mkNode(
                MINUS,
                nm->mkNode(
                    PLUS, nm->mkNode(MULT, b_v, a), nm->mkNode(MULT, a_v, b)),
                nm->mkNode(MULT, a_v, b_v));
            // conjuncts of the tangent plane lemma
            std::vector<Node> tplaneConj;
            for (unsigned d = 0; d < 4; d++)
            {
              Node aa = nm->mkNode(d == 0 || d == 3 ? GEQ : LEQ, a, a_v);
              Node ab = nm->mkNode(d == 1 || d == 3 ? GEQ : LEQ, b, b_v);
              Node conc = nm->mkNode(d <= 1 ? LEQ : GEQ, t, tplane);
              Node tlem = nm->mkNode(OR, aa.negate(), ab.negate(), conc);
              Trace("nl-ext-tplanes")
                  << "Tangent plane lemma : " << tlem << std::endl;
              tplaneConj.push_back(tlem);
            }

            // tangent plane reverse implication

            // t <= tplane -> ( (a <= a_v ^ b >= b_v) v
            // (a >= a_v ^ b <= b_v) ).
            // in clause form, the above becomes
            // t <= tplane -> a <= a_v v b <= b_v.
            // t <= tplane -> b >= b_v v a >= a_v.
            Node a_leq_av = nm->mkNode(LEQ, a, a_v);
            Node b_leq_bv = nm->mkNode(LEQ, b, b_v);
            Node a_geq_av = nm->mkNode(GEQ, a, a_v);
            Node b_geq_bv = nm->mkNode(GEQ, b, b_v);

            Node t_leq_tplane = nm->mkNode(LEQ, t, tplane);
            Node a_leq_av_or_b_leq_bv = nm->mkNode(OR, a_leq_av, b_leq_bv);
            Node b_geq_bv_or_a_geq_av = nm->mkNode(OR, b_geq_bv, a_geq_av);
            Node ub_reverse1 =
                nm->mkNode(OR, t_leq_tplane.negate(), a_leq_av_or_b_leq_bv);
            Trace("nl-ext-tplanes")
                << "Tangent plane lemma (reverse) : " << ub_reverse1
                << std::endl;
            tplaneConj.push_back(ub_reverse1);
            Node ub_reverse2 =
                nm->mkNode(OR, t_leq_tplane.negate(), b_geq_bv_or_a_geq_av);
            Trace("nl-ext-tplanes")
                << "Tangent plane lemma (reverse) : " << ub_reverse2
                << std::endl;
            tplaneConj.push_back(ub_reverse2);

            // t >= tplane -> ( (a <= a_v ^ b <= b_v) v
            // (a >= a_v ^ b >= b_v) ).
            // in clause form, the above becomes
            // t >= tplane -> a <= a_v v b >= b_v.
            // t >= tplane -> b >= b_v v a <= a_v
            Node t_geq_tplane = nm->mkNode(GEQ, t, tplane);
            Node a_leq_av_or_b_geq_bv = nm->mkNode(OR, a_leq_av, b_geq_bv);
            Node a_geq_av_or_b_leq_bv = nm->mkNode(OR, a_geq_av, b_leq_bv);
            Node lb_reverse1 =
                nm->mkNode(OR, t_geq_tplane.negate(), a_leq_av_or_b_geq_bv);
            Trace("nl-ext-tplanes")
                << "Tangent plane lemma (reverse) : " << lb_reverse1
                << std::endl;
            tplaneConj.push_back(lb_reverse1);
            Node lb_reverse2 =
                nm->mkNode(OR, t_geq_tplane.negate(), a_geq_av_or_b_leq_bv);
            Trace("nl-ext-tplanes")
                << "Tangent plane lemma (reverse) : " << lb_reverse2
                << std::endl;
            tplaneConj.push_back(lb_reverse2);

            Node tlem = nm->mkNode(AND, tplaneConj);
            lemmas.emplace_back(tlem, Inference::TANGENT_PLANE);
          }
        }
      }
    }
  }
  Trace("nl-ext") << "...trying " << lemmas.size() << " tangent plane lemmas..."
                  << std::endl;
  return lemmas;
}

std::vector<NlLemma> NlSolver::checkMonomialInferBounds(
    std::vector<NlLemma>& nt_lemmas,
    const std::vector<Node>& asserts,
    const std::vector<Node>& false_asserts)
{
  // sort monomials by degree
  Trace("nl-ext-proc") << "Sort monomials by degree..." << std::endl;
  d_mdb.sortByDegree(d_ms);
  // all monomials
  d_mterms.insert(d_mterms.end(), d_ms_vars.begin(), d_ms_vars.end());
  d_mterms.insert(d_mterms.end(), d_ms.begin(), d_ms.end());

  const std::map<Node, std::map<Node, ConstraintInfo> >& cim =
      d_cdb.getConstraints();

  std::vector<NlLemma> lemmas;
  NodeManager* nm = NodeManager::currentNM();
  // register constraints
  Trace("nl-ext-debug") << "Register bound constraints..." << std::endl;
  for (const Node& lit : asserts)
  {
    bool polarity = lit.getKind() != NOT;
    Node atom = lit.getKind() == NOT ? lit[0] : lit;
    d_cdb.registerConstraint(atom);
    bool is_false_lit =
        std::find(false_asserts.begin(), false_asserts.end(), lit)
        != false_asserts.end();
    // add information about bounds to variables
    std::map<Node, std::map<Node, ConstraintInfo> >::const_iterator itc =
        cim.find(atom);
    if (itc == cim.end())
    {
      continue;
    }
    for (const std::pair<const Node, ConstraintInfo>& itcc : itc->second)
    {
      Node x = itcc.first;
      Node coeff = itcc.second.d_coeff;
      Node rhs = itcc.second.d_rhs;
      Kind type = itcc.second.d_type;
      Node exp = lit;
      if (!polarity)
      {
        // reverse
        if (type == EQUAL)
        {
          // we will take the strict inequality in the direction of the
          // model
          Node lhs = ArithMSum::mkCoeffTerm(coeff, x);
          Node query = nm->mkNode(GT, lhs, rhs);
          Node query_mv = d_model.computeAbstractModelValue(query);
          if (query_mv == d_true)
          {
            exp = query;
            type = GT;
          }
          else
          {
            Assert(query_mv == d_false);
            exp = nm->mkNode(LT, lhs, rhs);
            type = LT;
          }
        }
        else
        {
          type = negateKind(type);
        }
      }
      // add to status if maximal degree
      d_ci_max[x][coeff][rhs] = d_cdb.isMaximal(atom, x);
      if (Trace.isOn("nl-ext-bound-debug2"))
      {
        Node t = ArithMSum::mkCoeffTerm(coeff, x);
        Trace("nl-ext-bound-debug2") << "Add Bound: " << t << " " << type << " "
                                     << rhs << " by " << exp << std::endl;
      }
      bool updated = true;
      std::map<Node, Kind>::iterator its = d_ci[x][coeff].find(rhs);
      if (its == d_ci[x][coeff].end())
      {
        d_ci[x][coeff][rhs] = type;
        d_ci_exp[x][coeff][rhs] = exp;
      }
      else if (type != its->second)
      {
        Trace("nl-ext-bound-debug2")
            << "Joining kinds : " << type << " " << its->second << std::endl;
        Kind jk = joinKinds(type, its->second);
        if (jk == UNDEFINED_KIND)
        {
          updated = false;
        }
        else if (jk != its->second)
        {
          if (jk == type)
          {
            d_ci[x][coeff][rhs] = type;
            d_ci_exp[x][coeff][rhs] = exp;
          }
          else
          {
            d_ci[x][coeff][rhs] = jk;
            d_ci_exp[x][coeff][rhs] =
                nm->mkNode(AND, d_ci_exp[x][coeff][rhs], exp);
          }
        }
        else
        {
          updated = false;
        }
      }
      if (Trace.isOn("nl-ext-bound"))
      {
        if (updated)
        {
          Trace("nl-ext-bound") << "Bound: ";
          debugPrintBound("nl-ext-bound", coeff, x, d_ci[x][coeff][rhs], rhs);
          Trace("nl-ext-bound") << " by " << d_ci_exp[x][coeff][rhs];
          if (d_ci_max[x][coeff][rhs])
          {
            Trace("nl-ext-bound") << ", is max degree";
          }
          Trace("nl-ext-bound") << std::endl;
        }
      }
      // compute if bound is not satisfied, and store what is required
      // for a possible refinement
      if (options::nlExtTangentPlanes())
      {
        if (is_false_lit)
        {
          d_tplane_refine.insert(x);
        }
      }
    }
  }
  // reflexive constraints
  Node null_coeff;
  for (unsigned j = 0; j < d_mterms.size(); j++)
  {
    Node n = d_mterms[j];
    d_ci[n][null_coeff][n] = EQUAL;
    d_ci_exp[n][null_coeff][n] = d_true;
    d_ci_max[n][null_coeff][n] = false;
  }

  Trace("nl-ext") << "Get inferred bound lemmas..." << std::endl;
  const std::map<Node, std::vector<Node> >& cpMap =
      d_mdb.getContainsParentMap();
  for (unsigned k = 0; k < d_mterms.size(); k++)
  {
    Node x = d_mterms[k];
    Trace("nl-ext-bound-debug")
        << "Process bounds for " << x << " : " << std::endl;
    std::map<Node, std::vector<Node> >::const_iterator itm = cpMap.find(x);
    if (itm == cpMap.end())
    {
      Trace("nl-ext-bound-debug") << "...has no parent monomials." << std::endl;
      continue;
    }
    Trace("nl-ext-bound-debug")
        << "...has " << itm->second.size() << " parent monomials." << std::endl;
    // check derived bounds
    std::map<Node, std::map<Node, std::map<Node, Kind> > >::iterator itc =
        d_ci.find(x);
    if (itc == d_ci.end())
    {
      continue;
    }
    for (std::map<Node, std::map<Node, Kind> >::iterator itcc =
             itc->second.begin();
         itcc != itc->second.end();
         ++itcc)
    {
      Node coeff = itcc->first;
      Node t = ArithMSum::mkCoeffTerm(coeff, x);
      for (std::map<Node, Kind>::iterator itcr = itcc->second.begin();
           itcr != itcc->second.end();
           ++itcr)
      {
        Node rhs = itcr->first;
        // only consider this bound if maximal degree
        if (!d_ci_max[x][coeff][rhs])
        {
          continue;
        }
        Kind type = itcr->second;
        for (unsigned j = 0; j < itm->second.size(); j++)
        {
          Node y = itm->second[j];
          Node mult = d_mdb.getContainsDiff(x, y);
          // x <k> t => m*x <k'> t  where y = m*x
          // get the sign of mult
          Node mmv = d_model.computeConcreteModelValue(mult);
          Trace("nl-ext-bound-debug2")
              << "Model value of " << mult << " is " << mmv << std::endl;
          if (!mmv.isConst())
          {
            Trace("nl-ext-bound-debug")
                << "     ...coefficient " << mult
                << " is non-constant (probably transcendental)." << std::endl;
            continue;
          }
          int mmv_sign = mmv.getConst<Rational>().sgn();
          Trace("nl-ext-bound-debug2")
              << "  sign of " << mmv << " is " << mmv_sign << std::endl;
          if (mmv_sign == 0)
          {
            Trace("nl-ext-bound-debug")
                << "     ...coefficient " << mult << " is zero." << std::endl;
            continue;
          }
          Trace("nl-ext-bound-debug")
              << "  from " << x << " * " << mult << " = " << y << " and " << t
              << " " << type << " " << rhs << ", infer : " << std::endl;
          Kind infer_type = mmv_sign == -1 ? reverseRelationKind(type) : type;
          Node infer_lhs = nm->mkNode(MULT, mult, t);
          Node infer_rhs = nm->mkNode(MULT, mult, rhs);
          Node infer = nm->mkNode(infer_type, infer_lhs, infer_rhs);
          Trace("nl-ext-bound-debug") << "     " << infer << std::endl;
          infer = Rewriter::rewrite(infer);
          Trace("nl-ext-bound-debug2")
              << "     ...rewritten : " << infer << std::endl;
          // check whether it is false in model for abstraction
          Node infer_mv = d_model.computeAbstractModelValue(infer);
          Trace("nl-ext-bound-debug")
              << "       ...infer model value is " << infer_mv << std::endl;
          if (infer_mv == d_false)
          {
            Node exp =
                nm->mkNode(AND,
                           nm->mkNode(mmv_sign == 1 ? GT : LT, mult, d_zero),
                           d_ci_exp[x][coeff][rhs]);
            Node iblem = nm->mkNode(IMPLIES, exp, infer);
            Node pr_iblem = iblem;
            iblem = Rewriter::rewrite(iblem);
            bool introNewTerms = hasNewMonomials(iblem, d_ms);
            Trace("nl-ext-bound-lemma")
                << "*** Bound inference lemma : " << iblem
                << " (pre-rewrite : " << pr_iblem << ")" << std::endl;
            // Trace("nl-ext-bound-lemma") << "       intro new
            // monomials = " << introNewTerms << std::endl;
            if (!introNewTerms)
            {
              lemmas.emplace_back(iblem, Inference::INFER_BOUNDS);
            }
            else
            {
              nt_lemmas.emplace_back(iblem, Inference::INFER_BOUNDS_NT);
            }
          }
        }
      }
    }
  }
  return lemmas;
}

std::vector<NlLemma> NlSolver::checkFactoring(
    const std::vector<Node>& asserts, const std::vector<Node>& false_asserts)
{
  std::vector<NlLemma> lemmas;
  NodeManager* nm = NodeManager::currentNM();
  Trace("nl-ext") << "Get factoring lemmas..." << std::endl;
  for (const Node& lit : asserts)
  {
    bool polarity = lit.getKind() != NOT;
    Node atom = lit.getKind() == NOT ? lit[0] : lit;
    Node litv = d_model.computeConcreteModelValue(lit);
    bool considerLit = false;
    // Only consider literals that are in false_asserts.
    considerLit = std::find(false_asserts.begin(), false_asserts.end(), lit)
                  != false_asserts.end();

    if (considerLit)
    {
      std::map<Node, Node> msum;
      if (ArithMSum::getMonomialSumLit(atom, msum))
      {
        Trace("nl-ext-factor") << "Factoring for literal " << lit
                               << ", monomial sum is : " << std::endl;
        if (Trace.isOn("nl-ext-factor"))
        {
          ArithMSum::debugPrintMonomialSum(msum, "nl-ext-factor");
        }
        std::map<Node, std::vector<Node> > factor_to_mono;
        std::map<Node, std::vector<Node> > factor_to_mono_orig;
        for (std::map<Node, Node>::iterator itm = msum.begin();
             itm != msum.end();
             ++itm)
        {
          if (!itm->first.isNull())
          {
            if (itm->first.getKind() == NONLINEAR_MULT)
            {
              std::vector<Node> children;
              for (unsigned i = 0; i < itm->first.getNumChildren(); i++)
              {
                children.push_back(itm->first[i]);
              }
              std::map<Node, bool> processed;
              for (unsigned i = 0; i < itm->first.getNumChildren(); i++)
              {
                if (processed.find(itm->first[i]) == processed.end())
                {
                  processed[itm->first[i]] = true;
                  children[i] = d_one;
                  if (!itm->second.isNull())
                  {
                    children.push_back(itm->second);
                  }
                  Node val = nm->mkNode(MULT, children);
                  if (!itm->second.isNull())
                  {
                    children.pop_back();
                  }
                  children[i] = itm->first[i];
                  val = Rewriter::rewrite(val);
                  factor_to_mono[itm->first[i]].push_back(val);
                  factor_to_mono_orig[itm->first[i]].push_back(itm->first);
                }
              }
            }
          }
        }
        for (std::map<Node, std::vector<Node> >::iterator itf =
                 factor_to_mono.begin();
             itf != factor_to_mono.end();
             ++itf)
        {
          Node x = itf->first;
          if (itf->second.size() == 1)
          {
            std::map<Node, Node>::iterator itm = msum.find(x);
            if (itm != msum.end())
            {
              itf->second.push_back(itm->second.isNull() ? d_one : itm->second);
              factor_to_mono_orig[x].push_back(x);
            }
          }
          if (itf->second.size() <= 1)
          {
            continue;
          }
          Node sum = nm->mkNode(PLUS, itf->second);
          sum = Rewriter::rewrite(sum);
          Trace("nl-ext-factor")
              << "* Factored sum for " << x << " : " << sum << std::endl;
          Node kf = getFactorSkolem(sum, lemmas);
          std::vector<Node> poly;
          poly.push_back(nm->mkNode(MULT, x, kf));
          std::map<Node, std::vector<Node> >::iterator itfo =
              factor_to_mono_orig.find(x);
          Assert(itfo != factor_to_mono_orig.end());
          for (std::map<Node, Node>::iterator itm = msum.begin();
               itm != msum.end();
               ++itm)
          {
            if (std::find(itfo->second.begin(), itfo->second.end(), itm->first)
                == itfo->second.end())
            {
              poly.push_back(ArithMSum::mkCoeffTerm(
                  itm->second, itm->first.isNull() ? d_one : itm->first));
            }
          }
          Node polyn = poly.size() == 1 ? poly[0] : nm->mkNode(PLUS, poly);
          Trace("nl-ext-factor")
              << "...factored polynomial : " << polyn << std::endl;
          Node conc_lit = nm->mkNode(atom.getKind(), polyn, d_zero);
          conc_lit = Rewriter::rewrite(conc_lit);
          if (!polarity)
          {
            conc_lit = conc_lit.negate();
          }

          std::vector<Node> lemma_disj;
          lemma_disj.push_back(lit.negate());
          lemma_disj.push_back(conc_lit);
          Node flem = nm->mkNode(OR, lemma_disj);
          Trace("nl-ext-factor") << "...lemma is " << flem << std::endl;
          lemmas.emplace_back(flem, Inference::FACTOR);
        }
      }
    }
  }
  return lemmas;
}

Node NlSolver::getFactorSkolem(Node n, std::vector<NlLemma>& lemmas)
{
  std::map<Node, Node>::iterator itf = d_factor_skolem.find(n);
  if (itf == d_factor_skolem.end())
  {
    NodeManager* nm = NodeManager::currentNM();
    Node k = nm->mkSkolem("kf", n.getType());
    Node k_eq = Rewriter::rewrite(k.eqNode(n));
    lemmas.push_back(k_eq);
    d_factor_skolem[n] = k;
    return k;
  }
  return itf->second;
}

std::vector<NlLemma> NlSolver::checkMonomialInferResBounds()
{
  std::vector<NlLemma> lemmas;
  NodeManager* nm = NodeManager::currentNM();
  Trace("nl-ext") << "Get monomial resolution inferred bound lemmas..."
                  << std::endl;
  size_t nmterms = d_mterms.size();
  for (unsigned j = 0; j < nmterms; j++)
  {
    Node a = d_mterms[j];
    std::map<Node, std::map<Node, std::map<Node, Kind> > >::iterator itca =
        d_ci.find(a);
    if (itca == d_ci.end())
    {
      continue;
    }
    for (unsigned k = (j + 1); k < nmterms; k++)
    {
      Node b = d_mterms[k];
      std::map<Node, std::map<Node, std::map<Node, Kind> > >::iterator itcb =
          d_ci.find(b);
      if (itcb == d_ci.end())
      {
        continue;
      }
      Trace("nl-ext-rbound-debug") << "resolution inferences : compare " << a
                                   << " and " << b << std::endl;
      // if they have common factors
      std::map<Node, Node>::iterator ita = d_mono_diff[a].find(b);
      if (ita == d_mono_diff[a].end())
      {
        continue;
      }
      Trace("nl-ext-rbound") << "Get resolution inferences for [a] " << a
                             << " vs [b] " << b << std::endl;
      std::map<Node, Node>::iterator itb = d_mono_diff[b].find(a);
      Assert(itb != d_mono_diff[b].end());
      Node mv_a = d_model.computeAbstractModelValue(ita->second);
      Assert(mv_a.isConst());
      int mv_a_sgn = mv_a.getConst<Rational>().sgn();
      if (mv_a_sgn == 0)
      {
        // we don't compare monomials whose current model value is zero
        continue;
      }
      Node mv_b = d_model.computeAbstractModelValue(itb->second);
      Assert(mv_b.isConst());
      int mv_b_sgn = mv_b.getConst<Rational>().sgn();
      if (mv_b_sgn == 0)
      {
        // we don't compare monomials whose current model value is zero
        continue;
      }
      Trace("nl-ext-rbound") << "  [a] factor is " << ita->second
                             << ", sign in model = " << mv_a_sgn << std::endl;
      Trace("nl-ext-rbound") << "  [b] factor is " << itb->second
                             << ", sign in model = " << mv_b_sgn << std::endl;

      std::vector<Node> exp;
      // bounds of a
      for (std::map<Node, std::map<Node, Kind> >::iterator itcac =
               itca->second.begin();
           itcac != itca->second.end();
           ++itcac)
      {
        Node coeff_a = itcac->first;
        for (std::map<Node, Kind>::iterator itcar = itcac->second.begin();
             itcar != itcac->second.end();
             ++itcar)
        {
          Node rhs_a = itcar->first;
          Node rhs_a_res_base = nm->mkNode(MULT, itb->second, rhs_a);
          rhs_a_res_base = Rewriter::rewrite(rhs_a_res_base);
          if (hasNewMonomials(rhs_a_res_base, d_ms))
          {
            continue;
          }
          Kind type_a = itcar->second;
          exp.push_back(d_ci_exp[a][coeff_a][rhs_a]);

          // bounds of b
          for (std::map<Node, std::map<Node, Kind> >::iterator itcbc =
                   itcb->second.begin();
               itcbc != itcb->second.end();
               ++itcbc)
          {
            Node coeff_b = itcbc->first;
            Node rhs_a_res = ArithMSum::mkCoeffTerm(coeff_b, rhs_a_res_base);
            for (std::map<Node, Kind>::iterator itcbr = itcbc->second.begin();
                 itcbr != itcbc->second.end();
                 ++itcbr)
            {
              Node rhs_b = itcbr->first;
              Node rhs_b_res = nm->mkNode(MULT, ita->second, rhs_b);
              rhs_b_res = ArithMSum::mkCoeffTerm(coeff_a, rhs_b_res);
              rhs_b_res = Rewriter::rewrite(rhs_b_res);
              if (hasNewMonomials(rhs_b_res, d_ms))
              {
                continue;
              }
              Kind type_b = itcbr->second;
              exp.push_back(d_ci_exp[b][coeff_b][rhs_b]);
              if (Trace.isOn("nl-ext-rbound"))
              {
                Trace("nl-ext-rbound") << "* try bounds : ";
                debugPrintBound("nl-ext-rbound", coeff_a, a, type_a, rhs_a);
                Trace("nl-ext-rbound") << std::endl;
                Trace("nl-ext-rbound") << "               ";
                debugPrintBound("nl-ext-rbound", coeff_b, b, type_b, rhs_b);
                Trace("nl-ext-rbound") << std::endl;
              }
              Kind types[2];
              for (unsigned r = 0; r < 2; r++)
              {
                Node pivot_factor = r == 0 ? itb->second : ita->second;
                int pivot_factor_sign = r == 0 ? mv_b_sgn : mv_a_sgn;
                types[r] = r == 0 ? type_a : type_b;
                if (pivot_factor_sign == (r == 0 ? 1 : -1))
                {
                  types[r] = reverseRelationKind(types[r]);
                }
                if (pivot_factor_sign == 1)
                {
                  exp.push_back(nm->mkNode(GT, pivot_factor, d_zero));
                }
                else
                {
                  exp.push_back(nm->mkNode(LT, pivot_factor, d_zero));
                }
              }
              Kind jk = transKinds(types[0], types[1]);
              Trace("nl-ext-rbound-debug")
                  << "trans kind : " << types[0] << " + " << types[1] << " = "
                  << jk << std::endl;
              if (jk != UNDEFINED_KIND)
              {
                Node conc = nm->mkNode(jk, rhs_a_res, rhs_b_res);
                Node conc_mv = d_model.computeAbstractModelValue(conc);
                if (conc_mv == d_false)
                {
                  Node rblem = nm->mkNode(IMPLIES, nm->mkNode(AND, exp), conc);
                  Trace("nl-ext-rbound-lemma-debug")
                      << "Resolution bound lemma "
                         "(pre-rewrite) "
                         ": "
                      << rblem << std::endl;
                  rblem = Rewriter::rewrite(rblem);
                  Trace("nl-ext-rbound-lemma")
                      << "Resolution bound lemma : " << rblem << std::endl;
                  lemmas.emplace_back(rblem, Inference::RES_INFER_BOUNDS);
                }
              }
              exp.pop_back();
              exp.pop_back();
              exp.pop_back();
            }
          }
          exp.pop_back();
        }
      }
    }
  }
  return lemmas;
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
