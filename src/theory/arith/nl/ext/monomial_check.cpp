/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Check for some monomial lemmas.
 */

#include "theory/arith/nl/ext/monomial_check.h"

#include "expr/node.h"
#include "proof/proof.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/ext/ext_state.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/arith/nl/nl_model.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

MonomialCheck::MonomialCheck(Env& env, ExtState* data)
    : EnvObj(env), d_data(data)
{
  d_order_points.push_back(d_data->d_neg_one);
  d_order_points.push_back(d_data->d_zero);
  d_order_points.push_back(d_data->d_one);
}

void MonomialCheck::init(const std::vector<Node>& xts)
{
  d_ms_proc.clear();
  d_m_nconst_factor.clear();

  for (unsigned i = 0, xsize = xts.size(); i < xsize; i++)
  {
    Node a = xts[i];
    if (a.getKind() == Kind::NONLINEAR_MULT)
    {
      const std::vector<Node>& varList = d_data->d_mdb.getVariableList(a);
      for (const Node& v : varList)
      {
        Node mvk = d_data->d_model.computeAbstractModelValue(v);
        if (!mvk.isConst())
        {
          d_m_nconst_factor[a] = true;
        }
      }
    }
  }

  for (unsigned j = 0; j < d_order_points.size(); j++)
  {
    Node c = d_order_points[j];
    d_data->d_model.computeConcreteModelValue(c);
    d_data->d_model.computeAbstractModelValue(c);
  }
}

void MonomialCheck::checkSign()
{
  std::map<Node, int> signs;
  Trace("nl-ext") << "Get monomial sign lemmas..." << std::endl;
  for (unsigned j = 0; j < d_data->d_ms.size(); j++)
  {
    Node a = d_data->d_ms[j];
    if (d_ms_proc.find(a) == d_ms_proc.end())
    {
      std::vector<Node> exp;
      if (TraceIsOn("nl-ext-debug"))
      {
        Node cmva = d_data->d_model.computeConcreteModelValue(a);
        Trace("nl-ext-debug")
            << "  process " << a << ", mv=" << cmva << "..." << std::endl;
      }
      if (d_m_nconst_factor.find(a) == d_m_nconst_factor.end())
      {
        signs[a] = compareSign(a, a, 0, 1, exp);
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
}

void MonomialCheck::checkMagnitude(unsigned c)
{
  // ensure information is setup
  if (c == 0)
  {
    Trace("nl-ext-proc") << "Assign order ids for " << d_data->d_ms_vars
                         << "..." << std::endl;
    // sort by absolute values of abstract model values
    assignOrderIds(d_data->d_ms_vars, d_order_vars, false, true);

    // sort individual variable lists
    Trace("nl-ext-proc") << "Assign order var lists for " << d_data->d_ms
                         << "..." << std::endl;
    d_data->d_mdb.sortVariablesByModel(d_data->d_ms, d_data->d_model);
  }

  unsigned r = 1;
  std::vector<SimpleTheoryLemma> lemmas;
  // if (x,y,L) in cmp_infers, then x > y inferred as conclusion of L
  // in lemmas
  std::map<int, std::map<Node, std::map<Node, Node> > > cmp_infers;
  Trace("nl-ext") << "Get monomial comparison lemmas (order=" << r
                  << ", compare=" << c << ")..." << std::endl;
  for (unsigned j = 0; j < d_data->d_ms.size(); j++)
  {
    Node a = d_data->d_ms[j];
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
                        d_data->d_one,
                        d_data->d_one,
                        b_exp_proc,
                        exp,
                        lemmas,
                        cmp_infers);
      }
      else
      {
        const NodeMultiset& mea = d_data->d_mdb.getMonomialExponentMap(a);
        if (c == 1)
        {
          // could compare not just against containing variables?
          // compare magnitude against variables
          for (unsigned k = 0; k < d_data->d_ms_vars.size(); k++)
          {
            Node v = d_data->d_ms_vars[k];
            Node mvcv = d_data->d_model.computeConcreteModelValue(v);
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
          for (unsigned k = (j + 1); k < d_data->d_ms.size(); k++)
          {
            Node b = d_data->d_ms[k];
            //(signs[a]==signs[b])==(r==0)
            if (d_ms_proc.find(b) == d_ms_proc.end()
                && d_m_nconst_factor.find(b) == d_m_nconst_factor.end())
            {
              const NodeMultiset& meb = d_data->d_mdb.getMonomialExponentMap(b);

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
  std::unordered_set<Node> r_lemmas;
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
  for (unsigned i = 0; i < lemmas.size(); i++)
  {
    if (r_lemmas.find(lemmas[i].d_node) == r_lemmas.end())
    {
      d_data->d_im.addPendingLemma(lemmas[i]);
    }
  }
  // could only take maximal lower/minimial lower bounds?
}

// show a <> 0 by inequalities between variables in monomial a w.r.t 0
int MonomialCheck::compareSign(
    Node oa, Node a, unsigned a_index, int status, std::vector<Node>& exp)
{
  Trace("nl-ext-debug") << "Process " << a << " at index " << a_index
                        << ", status is " << status << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  Node mvaoa = d_data->d_model.computeAbstractModelValue(oa);
  const std::vector<Node>& vla = d_data->d_mdb.getVariableList(a);
  if (a_index == vla.size())
  {
    if (mvaoa.getConst<Rational>().sgn() != status)
    {
      Node zero = mkZero(oa.getType());
      Node lemma = nm->mkAnd(exp).impNode(mkLit(oa, zero, status * 2));
      CDProof* proof = nullptr;
      if (d_data->isProofEnabled())
      {
        proof = d_data->getProof();
        std::vector<Node> args = exp;
        args.emplace_back(oa);
        proof->addStep(lemma, PfRule::ARITH_MULT_SIGN, {}, args);
      }
      d_data->d_im.addPendingLemma(lemma, InferenceId::ARITH_NL_SIGN, proof);
    }
    return status;
  }
  Assert(a_index < vla.size());
  Node av = vla[a_index];
  Node zero = mkZero(av.getType());
  unsigned aexp = d_data->d_mdb.getExponent(a, av);
  // take current sign in model
  Node mvaav = d_data->d_model.computeAbstractModelValue(av);
  int sgn = mvaav.getConst<Rational>().sgn();
  Trace("nl-ext-debug") << "Process var " << av << "^" << aexp
                        << ", model sign = " << sgn << std::endl;
  if (sgn == 0)
  {
    if (mvaoa.getConst<Rational>().sgn() != 0)
    {
      Node prem = av.eqNode(zero);
      Node conc = oa.eqNode(mkZero(oa.getType()));
      Node lemma = prem.impNode(conc);
      CDProof* proof = nullptr;
      if (d_data->isProofEnabled())
      {
        proof = d_data->getProof();
        proof->addStep(conc, PfRule::MACRO_SR_PRED_INTRO, {prem}, {conc});
        proof->addStep(lemma, PfRule::SCOPE, {conc}, {prem});
      }
      d_data->d_im.addPendingLemma(lemma, InferenceId::ARITH_NL_SIGN, proof);
    }
    return 0;
  }
  if (aexp % 2 == 0)
  {
    exp.push_back(av.eqNode(zero).negate());
    return compareSign(oa, a, a_index + 1, status, exp);
  }
  exp.push_back(nm->mkNode(sgn == 1 ? Kind::GT : Kind::LT, av, zero));
  return compareSign(oa, a, a_index + 1, status * sgn, exp);
}

bool MonomialCheck::compareMonomial(
    Node oa,
    Node a,
    NodeMultiset& a_exp_proc,
    Node ob,
    Node b,
    NodeMultiset& b_exp_proc,
    std::vector<Node>& exp,
    std::vector<SimpleTheoryLemma>& lem,
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

// trying to show a ( >, = ) b   by inequalities between variables in
// monomials a,b
bool MonomialCheck::compareMonomial(
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
    std::vector<SimpleTheoryLemma>& lem,
    std::map<int, std::map<Node, std::map<Node, Node> > >& cmp_infers)
{
  Trace("nl-ext-comp-debug")
      << "compareMonomial " << oa << " and " << ob << ", indices = " << a_index
      << " " << b_index << std::endl;
  Assert(status == 0 || status == 2);
  NodeManager* nm = NodeManager::currentNM();
  const std::vector<Node>& vla = d_data->d_mdb.getVariableList(a);
  const std::vector<Node>& vlb = d_data->d_mdb.getVariableList(b);
  if (a_index == vla.size() && b_index == vlb.size())
  {
    // finished, compare absolute value of abstract model values
    int modelStatus = d_data->d_model.compare(oa, ob, false, true) * 2;
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
        for (const Node& v : vla)
        {
          exp.push_back(v.eqNode(mkZero(v.getType())).negate());
        }
      }
      Node clem = nm->mkNode(
          Kind::IMPLIES, nm->mkAnd(exp), mkLit(oa, ob, status, true));
      Trace("nl-ext-comp-lemma") << "comparison lemma : " << clem << std::endl;
      lem.emplace_back(
          InferenceId::ARITH_NL_COMPARISON, clem, LemmaProperty::NONE, nullptr);
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
    unsigned aexpTotal = d_data->d_mdb.getExponent(a, av);
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
    Assert(d_order_vars.find(av) != d_order_vars.end())
        << "Missing order information for variable " << av;
    avo = d_order_vars[av];
  }
  Node bv;
  unsigned bexp = 0;
  unsigned bvo = 0;
  if (b_index < vlb.size())
  {
    bv = vlb[b_index];
    unsigned bexpTotal = d_data->d_mdb.getExponent(b, bv);
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
  Assert(d_order_vars.find(d_data->d_one) != d_order_vars.end());
  unsigned ovo = d_order_vars[d_data->d_one];
  Trace("nl-ext-comp-debug") << "....vars : " << av << "^" << aexp << " " << bv
                             << "^" << bexp << std::endl;

  //--- cases
  if (av.isNull())
  {
    if (bvo <= ovo)
    {
      Trace("nl-ext-comp-debug") << "...take leading " << bv << std::endl;
      // can multiply b by <=1
      Node one = mkOne(bv.getType());
      exp.push_back(mkLit(one, bv, bvo == ovo ? 0 : 2, true));
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
      Node one = mkOne(av.getType());
      exp.push_back(mkLit(av, one, avo == ovo ? 0 : 2, true));
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
      Node one = mkOne(av.getType());
      exp.push_back(mkLit(av, one, avo == ovo ? 0 : 2, true));
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
    exp.push_back(mkLit(d_data->d_one, bv, bvo == ovo ? 0 : 2, true));
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

bool MonomialCheck::cmp_holds(Node x,
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

void MonomialCheck::assignOrderIds(std::vector<Node>& vars,
                                   NodeMultiset& order,
                                   bool isConcrete,
                                   bool isAbsolute)
{
  SortNlModel smv;
  smv.d_nlm = &d_data->d_model;
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
    Node v = d_data->d_model.computeModelValue(x, isConcrete);
    if (!v.isConst())
    {
      Trace("nl-ext-mvo") << "..do not assign order to " << x << " : " << v
                          << std::endl;
      // don't assign for non-constant values (transcendental function apps)
      continue;
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
          Node vv = d_data->d_model.computeModelValue(
              d_order_points[order_index], isConcrete);
          if (d_data->d_model.compareValue(v, vv, isAbsolute) >= 0)
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
    if (prev.isNull() || d_data->d_model.compareValue(v, prev, isAbsolute) != 0)
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
Node MonomialCheck::mkLit(Node a, Node b, int status, bool isAbsolute) const
{
  NodeManager* nm = NodeManager::currentNM();
  Assert(a.getType().isRealOrInt() && b.getType().isRealOrInt());
  if (status == 0)
  {
    Node a_eq_b = mkEquality(a, b);
    if (!isAbsolute)
    {
      return a_eq_b;
    }
    Node negate_b = nm->mkNode(Kind::NEG, b);
    return a_eq_b.orNode(mkEquality(a, negate_b));
  }
  else if (status < 0)
  {
    return mkLit(b, a, -status);
  }
  Assert(status == 1 || status == 2);
  Kind greater_op = status == 1 ? Kind::GEQ : Kind::GT;
  if (!isAbsolute)
  {
    return nm->mkNode(greater_op, a, b);
  }
  // return nm->mkNode( greater_op, mkAbs( a ), mkAbs( b ) );
  Node zero = mkZero(a.getType());
  Node a_is_nonnegative = nm->mkNode(Kind::GEQ, a, zero);
  Node b_is_nonnegative = nm->mkNode(Kind::GEQ, b, zero);
  Node negate_a = nm->mkNode(Kind::NEG, a);
  Node negate_b = nm->mkNode(Kind::NEG, b);
  return a_is_nonnegative.iteNode(
      b_is_nonnegative.iteNode(nm->mkNode(greater_op, a, b),
                               nm->mkNode(greater_op, a, negate_b)),
      b_is_nonnegative.iteNode(nm->mkNode(greater_op, negate_a, b),
                               nm->mkNode(greater_op, negate_a, negate_b)));
}

void MonomialCheck::setMonomialFactor(Node a,
                                      Node b,
                                      const NodeMultiset& common)
{
  // Could not tell if this was being inserted intentionally or not.
  std::map<Node, Node>& mono_diff_a = d_data->d_mono_diff[a];
  if (mono_diff_a.find(b) == mono_diff_a.end())
  {
    Trace("nl-ext-mono-factor")
        << "Set monomial factor for " << a << "/" << b << std::endl;
    mono_diff_a[b] = d_data->d_mdb.mkMonomialRemFactor(a, common);
  }
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
