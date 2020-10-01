/*********************                                                        */
/*! \file cardinality_extension.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mudathir Mohamed, Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of an extension of the theory sets for handling
 ** cardinality constraints.
 **/

#include "theory/sets/cardinality_extension.h"

#include "expr/emptyset.h"
#include "expr/node_algorithm.h"
#include "options/sets_options.h"
#include "smt/logic_exception.h"
#include "theory/sets/normal_form.h"
#include "theory/theory_model.h"
#include "theory/valuation.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace sets {

CardinalityExtension::CardinalityExtension(SolverState& s,
                                           InferenceManager& im,
                                           TermRegistry& treg)
    : d_state(s),
      d_im(im),
      d_treg(treg),
      d_card_processed(s.getUserContext()),
      d_finite_type_constants_processed(false)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
}

void CardinalityExtension::reset()
{
  d_eqc_to_card_term.clear();
  d_t_card_enabled.clear();
  d_finite_type_elements.clear();
  d_finite_type_slack_elements.clear();
  d_univProxy.clear();
}
void CardinalityExtension::registerTerm(Node n)
{
  Trace("sets-card-debug") << "Register term : " << n << std::endl;
  Assert(n.getKind() == CARD);
  TypeNode tnc = n[0].getType().getSetElementType();
  d_t_card_enabled[tnc] = true;
  Node r = d_state.getRepresentative(n[0]);
  if (d_eqc_to_card_term.find(r) == d_eqc_to_card_term.end())
  {
    d_eqc_to_card_term[r] = n;
    registerCardinalityTerm(n[0]);
  }
  Trace("sets-card-debug") << "...finished register term" << std::endl;
}

void CardinalityExtension::checkCardinalityExtended()
{
  for (std::pair<const TypeNode, bool>& pair : d_t_card_enabled)
  {
    TypeNode type = pair.first;
    if (pair.second)
    {
      checkCardinalityExtended(type);
    }
  }
}

void CardinalityExtension::checkCardinalityExtended(TypeNode& t)
{
  NodeManager* nm = NodeManager::currentNM();
  TypeNode setType = nm->mkSetType(t);
  // skip infinite types that do not have univset terms
  if (!t.isInterpretedFinite() && d_state.getUnivSetEqClass(setType).isNull())
  {
    return;
  }

  // get the cardinality of the finite type t
  Cardinality card = t.getCardinality();

  // cardinality of an interpreted finite type t is infinite when t
  // is infinite without --fmf
  if (t.isInterpretedFinite() && card.isInfinite())
  {
    // TODO (#1123): support uninterpreted sorts with --finite-model-find
    std::stringstream message;
    message << "The cardinality " << card << " of the finite type " << t
            << " is not supported yet.";
    throw LogicException(message.str());
  }

  // here we call getUnivSet instead of getUnivSetEqClass to generate
  // a univset term for finite types even if they are not used in the input
  Node univ = d_treg.getUnivSet(setType);
  std::map<Node, Node>::iterator it = d_univProxy.find(univ);

  Node proxy;

  if (it == d_univProxy.end())
  {
    // Force cvc4 to build the cardinality graph for the universe set
    proxy = d_treg.getProxy(univ);
    d_univProxy[univ] = proxy;
  }
  else
  {
    proxy = it->second;
  }

  // get all equivalent classes of type t
  vector<Node> representatives = d_state.getSetsEqClasses(t);

  if (t.isInterpretedFinite())
  {
    Node typeCardinality = nm->mkConst(Rational(card.getFiniteCardinality()));
    Node cardUniv = nm->mkNode(kind::CARD, proxy);
    Node leq = nm->mkNode(kind::LEQ, cardUniv, typeCardinality);

    // (=> true (<= (card (as univset t)) cardUniv)
    if (!d_state.isEntailed(leq, true))
    {
      d_im.assertInference(
          leq, d_true, "univset cardinality <= type cardinality", 1);
    }
  }

  // add subset lemmas for sets and membership lemmas for negative members
  for (Node& representative : representatives)
  {
    // the universe set is a subset of itself
    if (representative != d_state.getRepresentative(univ))
    {
      // here we only add representatives with variables to avoid adding
      // infinite equivalent generated terms to the cardinality graph
      Node variable = d_state.getVariableSet(representative);
      if (variable.isNull())
      {
        continue;
      }

      // (=> true (subset representative (as univset t))
      Node subset = nm->mkNode(kind::SUBSET, variable, proxy);
      // subset terms are rewritten as union terms: (subset A B) implies (=
      // (union A B) B)
      subset = Rewriter::rewrite(subset);
      if (!d_state.isEntailed(subset, true))
      {
        d_im.assertInference(subset, d_true, "univset is a super set", 1);
      }

      // negative members are members in the universe set
      const std::map<Node, Node>& negativeMembers =
          d_state.getNegativeMembers(representative);

      for (const std::pair<Node, Node>& negativeMember : negativeMembers)
      {
        Node member = nm->mkNode(MEMBER, negativeMember.first, univ);
        // negativeMember.second is the reason for the negative membership and
        // has kind MEMBER. So we specify the negation as the reason for the
        // negative membership lemma
        Node notMember = nm->mkNode(NOT, negativeMember.second);
        // (=>
        //    (not (member negativeMember representative)))
        //    (member negativeMember (as univset t)))
        d_im.assertInference(
            member, notMember, "negative members are in the universe", 1);
      }
    }
  }
}

void CardinalityExtension::check()
{
  checkCardinalityExtended();
  checkRegister();
  if (d_im.hasSent())
  {
    return;
  }
  checkMinCard();
  if (d_im.hasSent())
  {
    return;
  }
  checkCardCycles();
  if (d_im.hasSent())
  {
    return;
  }
  // The last step will either do nothing (in which case we are SAT), or request
  // that a new set term is introduced.
  std::vector<Node> intro_sets;
  checkNormalForms(intro_sets);
  if (intro_sets.empty())
  {
    return;
  }
  Assert(intro_sets.size() == 1);
  Trace("sets-intro") << "Introduce term : " << intro_sets[0] << std::endl;
  Trace("sets-intro") << "  Actual Intro : ";
  d_treg.debugPrintSet(intro_sets[0], "sets-nf");
  Trace("sets-nf") << std::endl;
  Node k = d_treg.getProxy(intro_sets[0]);
  AlwaysAssert(!k.isNull());
}

void CardinalityExtension::checkRegister()
{
  Trace("sets") << "Cardinality graph..." << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  // first, ensure cardinality relationships are added as lemmas for all
  // non-basic set terms
  const std::vector<Node>& setEqc = d_state.getSetsEqClasses();
  for (const Node& eqc : setEqc)
  {
    const std::vector<Node>& nvsets = d_state.getNonVariableSets(eqc);
    for (Node n : nvsets)
    {
      if (!d_state.isCongruent(n))
      {
        // if setminus, do for intersection instead
        if (n.getKind() == SETMINUS)
        {
          n = Rewriter::rewrite(nm->mkNode(INTERSECTION, n[0], n[1]));
        }
        registerCardinalityTerm(n);
      }
    }
  }
  Trace("sets") << "Done cardinality graph" << std::endl;
}

void CardinalityExtension::registerCardinalityTerm(Node n)
{
  TypeNode tnc = n.getType().getSetElementType();
  if (d_t_card_enabled.find(tnc) == d_t_card_enabled.end())
  {
    // if no cardinality constraints for sets of this type, we can ignore
    return;
  }
  if (d_card_processed.find(n) != d_card_processed.end())
  {
    // already processed
    return;
  }
  d_card_processed.insert(n);
  NodeManager* nm = NodeManager::currentNM();
  Trace("sets-card") << "Cardinality lemmas for " << n << " : " << std::endl;
  std::vector<Node> cterms;
  if (n.getKind() == INTERSECTION)
  {
    for (unsigned e = 0; e < 2; e++)
    {
      Node s = nm->mkNode(SETMINUS, n[e], n[1 - e]);
      cterms.push_back(s);
    }
    Node pos_lem = nm->mkNode(GEQ, nm->mkNode(CARD, n), d_zero);
    d_im.assertInference(pos_lem, d_emp_exp, "pcard", 1);
  }
  else
  {
    cterms.push_back(n);
  }
  for (unsigned k = 0, csize = cterms.size(); k < csize; k++)
  {
    Node nn = cterms[k];
    Node nk = d_treg.getProxy(nn);
    Node pos_lem = nm->mkNode(GEQ, nm->mkNode(CARD, nk), d_zero);
    d_im.assertInference(pos_lem, d_emp_exp, "pcard", 1);
    if (nn != nk)
    {
      Node lem = nm->mkNode(EQUAL, nm->mkNode(CARD, nk), nm->mkNode(CARD, nn));
      lem = Rewriter::rewrite(lem);
      Trace("sets-card") << "  " << k << " : " << lem << std::endl;
      d_im.assertInference(lem, d_emp_exp, "card", 1);
    }
  }
  d_im.doPendingLemmas();
}

void CardinalityExtension::checkCardCycles()
{
  Trace("sets") << "Check cardinality cycles..." << std::endl;
  // build order of equivalence classes, also build cardinality graph
  const std::vector<Node>& setEqc = d_state.getSetsEqClasses();
  d_oSetEqc.clear();
  d_card_parent.clear();
  for (const Node& s : setEqc)
  {
    std::vector<Node> curr;
    std::vector<Node> exp;
    checkCardCyclesRec(s, curr, exp);
    if (d_im.hasSent())
    {
      return;
    }
  }
  Trace("sets") << "Done check cardinality cycles" << std::endl;
}

void CardinalityExtension::checkCardCyclesRec(Node eqc,
                                              std::vector<Node>& curr,
                                              std::vector<Node>& exp)
{
  Trace("sets-cycle-debug") << "Traverse eqc " << eqc << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  if (std::find(curr.begin(), curr.end(), eqc) != curr.end())
  {
    Trace("sets-debug") << "Found venn region loop..." << std::endl;
    if (curr.size() > 1)
    {
      // all regions must be equal
      std::vector<Node> conc;
      bool foundLoopStart = false;
      for (const Node& cc : curr)
      {
        if (cc == eqc)
        {
          foundLoopStart = true;
        }
        else if (foundLoopStart && eqc != cc)
        {
          conc.push_back(eqc.eqNode(cc));
        }
      }
      Node fact = conc.size() == 1 ? conc[0] : nm->mkNode(AND, conc);
      Trace("sets-cycle-debug")
          << "CYCLE: " << fact << " from " << exp << std::endl;
      d_im.assertInference(fact, exp, "card_cycle");
      d_im.doPendingLemmas();
    }
    else
    {
      // should be guaranteed based on not exploring equal parents
      Assert(false);
    }
    return;
  }
  if (std::find(d_oSetEqc.begin(), d_oSetEqc.end(), eqc) != d_oSetEqc.end())
  {
    // already processed
    return;
  }
  const std::vector<Node>& nvsets = d_state.getNonVariableSets(eqc);
  if (nvsets.empty())
  {
    // no non-variable sets, trivial
    d_oSetEqc.push_back(eqc);
    return;
  }
  curr.push_back(eqc);
  TypeNode tn = eqc.getType();
  bool is_empty = eqc == d_state.getEmptySetEqClass(tn);
  Node emp_set = d_treg.getEmptySet(tn);
  for (const Node& n : nvsets)
  {
    Kind nk = n.getKind();
    if (nk != INTERSECTION && nk != SETMINUS)
    {
      continue;
    }
    Trace("sets-debug") << "Build cardinality parents for " << n << "..."
                        << std::endl;
    std::vector<Node> sib;
    unsigned true_sib = 0;
    if (n.getKind() == INTERSECTION)
    {
      d_localBase[n] = n;
      for (unsigned e = 0; e < 2; e++)
      {
        Node sm = Rewriter::rewrite(nm->mkNode(SETMINUS, n[e], n[1 - e]));
        sib.push_back(sm);
      }
      true_sib = 2;
    }
    else
    {
      Node si = Rewriter::rewrite(nm->mkNode(INTERSECTION, n[0], n[1]));
      sib.push_back(si);
      d_localBase[n] = si;
      Node osm = Rewriter::rewrite(nm->mkNode(SETMINUS, n[1], n[0]));
      sib.push_back(osm);
      true_sib = 1;
    }
    Node u = Rewriter::rewrite(nm->mkNode(UNION, n[0], n[1]));
    if (!d_state.hasTerm(u))
    {
      u = Node::null();
    }
    unsigned n_parents = true_sib + (u.isNull() ? 0 : 1);
    // if this set is empty
    if (is_empty)
    {
      Assert(d_state.areEqual(n, emp_set));
      Trace("sets-debug") << "  empty, parents equal siblings" << std::endl;
      std::vector<Node> conc;
      // parent equal siblings
      for (unsigned e = 0; e < true_sib; e++)
      {
        if (d_state.hasTerm(sib[e]) && !d_state.areEqual(n[e], sib[e]))
        {
          conc.push_back(n[e].eqNode(sib[e]));
        }
      }
      d_im.assertInference(conc, n.eqNode(emp_set), "cg_emp");
      d_im.doPendingLemmas();
      if (d_im.hasSent())
      {
        return;
      }
      else
      {
        // justify why there is no edge to parents (necessary?)
        for (unsigned e = 0; e < n_parents; e++)
        {
          Node p = (e == true_sib) ? u : n[e];
        }
      }
      continue;
    }
    std::vector<Node> card_parents;
    std::vector<int> card_parent_ids;
    // check if equal to a parent
    for (unsigned e = 0; e < n_parents; e++)
    {
      Trace("sets-debug") << "  check parent " << e << "/" << n_parents
                          << std::endl;
      bool is_union = e == true_sib;
      Node p = (e == true_sib) ? u : n[e];
      Trace("sets-debug") << "  check relation to parent " << p
                          << ", isu=" << is_union << "..." << std::endl;
      // if parent is empty
      if (d_state.areEqual(p, emp_set))
      {
        Trace("sets-debug") << "  it is empty..." << std::endl;
        Assert(!d_state.areEqual(n, emp_set));
        d_im.assertInference(n.eqNode(emp_set), p.eqNode(emp_set), "cg_emppar");
        d_im.doPendingLemmas();
        if (d_im.hasSent())
        {
          return;
        }
        // if we are equal to a parent
      }
      else if (d_state.areEqual(p, n))
      {
        Trace("sets-debug") << "  it is equal to this..." << std::endl;
        std::vector<Node> conc;
        std::vector<int> sib_emp_indices;
        if (is_union)
        {
          for (unsigned s = 0; s < sib.size(); s++)
          {
            sib_emp_indices.push_back(s);
          }
        }
        else
        {
          sib_emp_indices.push_back(e);
        }
        // sibling(s) are empty
        for (unsigned si : sib_emp_indices)
        {
          if (!d_state.areEqual(sib[si], emp_set))
          {
            conc.push_back(sib[si].eqNode(emp_set));
          }
          else
          {
            Trace("sets-debug")
                << "Sibling " << sib[si] << " is already empty." << std::endl;
          }
        }
        if (!is_union && nk == INTERSECTION && !u.isNull())
        {
          // union is equal to other parent
          if (!d_state.areEqual(u, n[1 - e]))
          {
            conc.push_back(u.eqNode(n[1 - e]));
          }
        }
        Trace("sets-debug")
            << "...derived " << conc.size() << " conclusions" << std::endl;
        d_im.assertInference(conc, n.eqNode(p), "cg_eqpar");
        d_im.doPendingLemmas();
        if (d_im.hasSent())
        {
          return;
        }
      }
      else
      {
        Trace("sets-cdg") << "Card graph : " << n << " -> " << p << std::endl;
        // otherwise, we a syntactic subset of p
        card_parents.push_back(p);
        card_parent_ids.push_back(is_union ? 2 : e);
      }
    }
    Assert(d_card_parent[n].empty());
    Trace("sets-debug") << "get parent representatives..." << std::endl;
    // for each parent, take their representatives
    for (unsigned k = 0, numcp = card_parents.size(); k < numcp; k++)
    {
      Node cpk = card_parents[k];
      Node eqcc = d_state.getRepresentative(cpk);
      Trace("sets-debug") << "Check card parent " << k << "/"
                          << card_parents.size() << std::endl;

      // if parent is singleton, then we should either be empty to equal to it
      Node eqccSingleton = d_state.getSingletonEqClass(eqcc);
      if (!eqccSingleton.isNull())
      {
        bool eq_parent = false;
        std::vector<Node> exps;
        d_state.addEqualityToExp(cpk, eqccSingleton, exps);
        if (d_state.areDisequal(n, emp_set))
        {
          exps.push_back(n.eqNode(emp_set).negate());
          eq_parent = true;
        }
        else
        {
          const std::map<Node, Node>& pmemsE = d_state.getMembers(eqc);
          if (!pmemsE.empty())
          {
            Node pmem = pmemsE.begin()->second;
            exps.push_back(pmem);
            d_state.addEqualityToExp(n, pmem[1], exps);
            eq_parent = true;
          }
        }
        // must be equal to parent
        if (eq_parent)
        {
          Node conc = n.eqNode(cpk);
          d_im.assertInference(conc, exps, "cg_par_sing");
          d_im.doPendingLemmas();
        }
        else
        {
          // split on empty
          Trace("sets-nf") << "Split empty : " << n << std::endl;
          d_im.split(n.eqNode(emp_set), 1);
        }
        Assert(d_im.hasSent());
        return;
      }
      else
      {
        bool dup = false;
        for (unsigned l = 0, numcpn = d_card_parent[n].size(); l < numcpn; l++)
        {
          Node cpnl = d_card_parent[n][l];
          if (eqcc != cpnl)
          {
            continue;
          }
          Trace("sets-debug") << "  parents " << l << " and " << k
                              << " are equal, ids = " << card_parent_ids[l]
                              << " " << card_parent_ids[k] << std::endl;
          dup = true;
          if (n.getKind() != INTERSECTION)
          {
            continue;
          }
          Assert(card_parent_ids[l] != 2);
          std::vector<Node> conc;
          if (card_parent_ids[k] == 2)
          {
            // intersection is equal to other parent
            unsigned pid = 1 - card_parent_ids[l];
            if (!d_state.areEqual(n[pid], n))
            {
              Trace("sets-debug")
                  << "  one of them is union, make equal to other..."
                  << std::endl;
              conc.push_back(n[pid].eqNode(n));
            }
          }
          else
          {
            if (!d_state.areEqual(cpk, n))
            {
              Trace("sets-debug")
                  << "  neither is union, make equal to one parent..."
                  << std::endl;
              // intersection is equal to one of the parents
              conc.push_back(cpk.eqNode(n));
            }
          }
          d_im.assertInference(conc, cpk.eqNode(cpnl), "cg_pareq");
          d_im.doPendingLemmas();
          if (d_im.hasSent())
          {
            return;
          }
        }
        if (!dup)
        {
          d_card_parent[n].push_back(eqcc);
        }
      }
    }
    // now recurse on parents (to ensure their normal will be computed after
    // this eqc)
    exp.push_back(eqc.eqNode(n));
    for (const Node& cpnc : d_card_parent[n])
    {
      Trace("sets-cycle-debug")
          << "Traverse card parent " << eqc << " -> " << cpnc << std::endl;
      checkCardCyclesRec(cpnc, curr, exp);
      if (d_im.hasSent())
      {
        return;
      }
    }
    exp.pop_back();
  }
  curr.pop_back();
  // parents now processed, can add to ordered list
  d_oSetEqc.push_back(eqc);
}

void CardinalityExtension::checkNormalForms(std::vector<Node>& intro_sets)
{
  Trace("sets") << "Check normal forms..." << std::endl;
  // now, build normal form for each equivalence class
  // d_oSetEqc is now sorted such that for each d_oSetEqc[i], d_oSetEqc[j],
  // if d_oSetEqc[i] is a strict syntactic subterm of d_oSetEqc[j], then i<j.
  d_ff.clear();
  d_nf.clear();
  for (int i = (int)(d_oSetEqc.size() - 1); i >= 0; i--)
  {
    checkNormalForm(d_oSetEqc[i], intro_sets);
    if (d_im.hasSent() || !intro_sets.empty())
    {
      return;
    }
  }
  Trace("sets") << "Done check normal forms" << std::endl;
}

void CardinalityExtension::checkNormalForm(Node eqc,
                                           std::vector<Node>& intro_sets)
{
  TypeNode tn = eqc.getType();
  Trace("sets") << "Compute normal form for " << eqc << std::endl;
  Trace("sets-nf") << "Compute N " << eqc << "..." << std::endl;
  if (eqc == d_state.getEmptySetEqClass(tn))
  {
    d_nf[eqc].clear();
    Trace("sets-nf") << "----> N " << eqc << " => {}" << std::endl;
    return;
  }
  // flat/normal forms are sets of equivalence classes
  Node base;
  std::vector<Node> comps;
  std::map<Node, std::map<Node, std::vector<Node> > >::iterator it =
      d_ff.find(eqc);
  if (it != d_ff.end())
  {
    for (std::pair<const Node, std::vector<Node> >& itf : it->second)
    {
      std::sort(itf.second.begin(), itf.second.end());
      if (base.isNull())
      {
        base = itf.first;
      }
      else
      {
        comps.push_back(itf.first);
      }
      Trace("sets-nf") << "  F " << itf.first << " : " << itf.second
                       << std::endl;
      Trace("sets-nf-debug") << " ...";
      d_treg.debugPrintSet(itf.first, "sets-nf-debug");
      Trace("sets-nf-debug") << std::endl;
    }
  }
  else
  {
    Trace("sets-nf") << "(no flat forms)" << std::endl;
  }
  std::map<Node, std::vector<Node> >& ffeqc = d_ff[eqc];
  Assert(d_nf.find(eqc) == d_nf.end());
  std::vector<Node>& nfeqc = d_nf[eqc];
  NodeManager* nm = NodeManager::currentNM();
  bool success = true;
  Node emp_set = d_treg.getEmptySet(tn);
  if (!base.isNull())
  {
    for (unsigned j = 0, csize = comps.size(); j < csize; j++)
    {
      // compare if equal
      std::vector<Node> c;
      c.push_back(base);
      c.push_back(comps[j]);
      std::vector<Node> only[2];
      std::vector<Node> common;
      Trace("sets-nf-debug") << "Compare venn regions of " << base << " vs "
                             << comps[j] << std::endl;
      unsigned k[2] = {0, 0};
      while (k[0] < ffeqc[c[0]].size() || k[1] < ffeqc[c[1]].size())
      {
        bool proc = true;
        for (unsigned e = 0; e < 2; e++)
        {
          if (k[e] == ffeqc[c[e]].size())
          {
            for (; k[1 - e] < ffeqc[c[1 - e]].size(); ++k[1 - e])
            {
              only[1 - e].push_back(ffeqc[c[1 - e]][k[1 - e]]);
            }
            proc = false;
          }
        }
        if (proc)
        {
          if (ffeqc[c[0]][k[0]] == ffeqc[c[1]][k[1]])
          {
            common.push_back(ffeqc[c[0]][k[0]]);
            k[0]++;
            k[1]++;
          }
          else if (ffeqc[c[0]][k[0]] < ffeqc[c[1]][k[1]])
          {
            only[0].push_back(ffeqc[c[0]][k[0]]);
            k[0]++;
          }
          else
          {
            only[1].push_back(ffeqc[c[1]][k[1]]);
            k[1]++;
          }
        }
      }
      if (!only[0].empty() || !only[1].empty())
      {
        if (Trace.isOn("sets-nf-debug"))
        {
          Trace("sets-nf-debug") << "Unique venn regions : " << std::endl;
          for (unsigned e = 0; e < 2; e++)
          {
            Trace("sets-nf-debug") << "  " << c[e] << " : { ";
            for (unsigned l = 0; l < only[e].size(); l++)
            {
              if (l > 0)
              {
                Trace("sets-nf-debug") << ", ";
              }
              Trace("sets-nf-debug") << "[" << only[e][l] << "]";
            }
            Trace("sets-nf-debug") << " }" << std::endl;
          }
        }
        // try to make one empty, prefer the unique ones first
        for (unsigned e = 0; e < 3; e++)
        {
          unsigned sz = e == 2 ? common.size() : only[e].size();
          for (unsigned l = 0; l < sz; l++)
          {
            Node r = e == 2 ? common[l] : only[e][l];
            Trace("sets-nf-debug") << "Try split empty : " << r << std::endl;
            Trace("sets-nf-debug") << "         actual : ";
            d_treg.debugPrintSet(r, "sets-nf-debug");
            Trace("sets-nf-debug") << std::endl;
            Assert(!d_state.areEqual(r, emp_set));
            if (!d_state.areDisequal(r, emp_set) && !d_state.hasMembers(r))
            {
              // guess that its equal empty if it has no explicit members
              Trace("sets-nf") << " Split empty : " << r << std::endl;
              Trace("sets-nf") << "Actual Split : ";
              d_treg.debugPrintSet(r, "sets-nf");
              Trace("sets-nf") << std::endl;
              d_im.split(r.eqNode(emp_set), 1);
              Assert(d_im.hasSent());
              return;
            }
          }
        }
        for (const Node& o0 : only[0])
        {
          for (const Node& o1 : only[1])
          {
            bool disjoint = false;
            Trace("sets-nf-debug")
                << "Try split " << o0 << " against " << o1 << std::endl;
            // split them
            for (unsigned e = 0; e < 2; e++)
            {
              Node r1 = e == 0 ? o0 : o1;
              Node r2 = e == 0 ? o1 : o0;
              // check if their intersection exists modulo equality
              Node r1r2i = d_state.getBinaryOpTerm(INTERSECTION, r1, r2);
              if (!r1r2i.isNull())
              {
                Trace("sets-nf-debug")
                    << "Split term already exists, but not in cardinality "
                       "graph : "
                    << r1r2i << ", should be empty." << std::endl;
                // their intersection is empty (probably?)
                // e.g. these are two disjoint venn regions, proceed to next
                // pair
                Assert(d_state.areEqual(emp_set, r1r2i));
                disjoint = true;
                break;
              }
            }
            if (!disjoint)
            {
              // simply introduce their intersection
              Assert(o0 != o1);
              Node kca = d_treg.getProxy(o0);
              Node kcb = d_treg.getProxy(o1);
              Node intro =
                  Rewriter::rewrite(nm->mkNode(INTERSECTION, kca, kcb));
              Trace("sets-nf") << "   Intro split : " << o0 << " against " << o1
                               << ", term is " << intro << std::endl;
              intro_sets.push_back(intro);
              Assert(!d_state.hasTerm(intro));
              return;
            }
          }
        }
        // should never get here
        success = false;
      }
    }
    if (success)
    {
      // normal form is flat form of base
      nfeqc.insert(nfeqc.end(), ffeqc[base].begin(), ffeqc[base].end());
      Trace("sets-nf") << "----> N " << eqc << " => F " << base << std::endl;
    }
    else
    {
      Trace("sets-nf") << "failed to build N " << eqc << std::endl;
    }
  }
  else
  {
    // must ensure disequal from empty
    if (!eqc.isConst() && !d_state.areDisequal(eqc, emp_set)
        && !d_state.hasMembers(eqc))
    {
      Trace("sets-nf-debug") << "Split on leaf " << eqc << std::endl;
      d_im.split(eqc.eqNode(emp_set));
      success = false;
    }
    else
    {
      // normal form is this equivalence class
      nfeqc.push_back(eqc);
      Trace("sets-nf") << "----> N " << eqc << " => { " << eqc << " }"
                       << std::endl;
    }
  }
  if (!success)
  {
    Assert(d_im.hasSent());
    return;
  }
  // Send to parents (a parent is a set that contains a term in this equivalence
  // class as a direct child).
  const std::vector<Node>& nvsets = d_state.getNonVariableSets(eqc);
  if (nvsets.empty())
  {
    // no non-variable sets
    return;
  }
  std::map<Node, std::map<Node, bool> > parents_proc;
  for (const Node& n : nvsets)
  {
    Trace("sets-nf-debug") << "Carry nf for term " << n << std::endl;
    if (d_card_parent[n].empty())
    {
      // nothing to do
      continue;
    }
    Assert(d_localBase.find(n) != d_localBase.end());
    Node cbase = d_localBase[n];
    Trace("sets-nf-debug") << "Card base is " << cbase << std::endl;
    for (const Node& p : d_card_parent[n])
    {
      Trace("sets-nf-debug") << "Check parent " << p << std::endl;
      if (parents_proc[cbase].find(p) != parents_proc[cbase].end())
      {
        Trace("sets-nf-debug") << "..already processed parent " << p << " for "
                               << cbase << std::endl;
        continue;
      }
      parents_proc[cbase][p] = true;
      Trace("sets-nf-debug") << "Carry nf to parent ( " << cbase << ", [" << p
                             << "] ), from " << n << "..." << std::endl;

      std::vector<Node>& ffpc = d_ff[p][cbase];
      for (const Node& nfeqci : nfeqc)
      {
        if (std::find(ffpc.begin(), ffpc.end(), nfeqci) == ffpc.end())
        {
          ffpc.insert(ffpc.end(), nfeqc.begin(), nfeqc.end());
        }
        else
        {
          // if it is a duplicate venn region, it must be empty since it is
          // coming from syntactically disjoint siblings
        }
      }
    }
  }
}

void CardinalityExtension::checkMinCard()
{
  NodeManager* nm = NodeManager::currentNM();
  const std::vector<Node>& setEqc = d_state.getSetsEqClasses();
  for (int i = (int)(setEqc.size() - 1); i >= 0; i--)
  {
    Node eqc = setEqc[i];
    TypeNode tn = eqc.getType().getSetElementType();
    if (d_t_card_enabled.find(tn) == d_t_card_enabled.end())
    {
      // cardinality is not enabled for this type, skip
      continue;
    }
    // get members in class
    const std::map<Node, Node>& pmemsE = d_state.getMembers(eqc);
    if (pmemsE.empty())
    {
      // no members, trivial
      continue;
    }
    std::vector<Node> exp;
    std::vector<Node> members;
    Node cardTerm;
    std::map<Node, Node>::iterator it = d_eqc_to_card_term.find(eqc);
    if (it != d_eqc_to_card_term.end())
    {
      cardTerm = it->second;
    }
    else
    {
      cardTerm = nm->mkNode(CARD, eqc);
    }
    for (const std::pair<const Node, Node>& itmm : pmemsE)
    {
      members.push_back(itmm.first);
      exp.push_back(nm->mkNode(MEMBER, itmm.first, cardTerm[0]));
    }
    if (members.size() > 1)
    {
      exp.push_back(nm->mkNode(DISTINCT, members));
    }
    if (!members.empty())
    {
      Node conc =
          nm->mkNode(GEQ, cardTerm, nm->mkConst(Rational(members.size())));
      Node expn = exp.size() == 1 ? exp[0] : nm->mkNode(AND, exp);
      d_im.assertInference(conc, expn, "mincard", 1);
    }
  }
  // flush the lemmas
  d_im.doPendingLemmas();
}

bool CardinalityExtension::isModelValueBasic(Node eqc)
{
  return d_nf[eqc].size() == 1 && d_nf[eqc][0] == eqc;
}

void CardinalityExtension::mkModelValueElementsFor(
    Valuation& val,
    Node eqc,
    std::vector<Node>& els,
    const std::map<Node, Node>& mvals,
    TheoryModel* model)
{
  TypeNode elementType = eqc.getType().getSetElementType();
  if (isModelValueBasic(eqc))
  {
    std::map<Node, Node>::iterator it = d_eqc_to_card_term.find(eqc);
    if (it != d_eqc_to_card_term.end())
    {
      // slack elements from cardinality value
      Node v = val.getModelValue(it->second);
      Trace("sets-model") << "Cardinality of " << eqc << " is " << v
                          << std::endl;
      if (v.getConst<Rational>() > UINT32_MAX)
      {
        std::stringstream ss;
        ss << "The model for " << eqc << " was computed to have cardinality "
           << v << ". We only allow sets up to cardinality " << UINT32_MAX;
        throw LogicException(ss.str());
      }
      std::uint32_t vu = v.getConst<Rational>().getNumerator().toUnsignedInt();
      Assert(els.size() <= vu);
      NodeManager* nm = NodeManager::currentNM();
      if (elementType.isInterpretedFinite())
      {
        // get all members of this finite type
        collectFiniteTypeSetElements(model);
      }
      while (els.size() < vu)
      {
        if (elementType.isInterpretedFinite())
        {
          // At this point we are sure the formula is satisfiable and all
          // cardinality constraints are satisfied. Since this type is finite,
          // there is only one single cardinality graph for all sets of this
          // type because the universe cardinality constraint has been added by
          // CardinalityExtension::checkCardinalityExtended. This means we have
          // enough slack elements of this finite type for all disjoint leaves
          // in the cardinality graph. Therefore we can safely add new distinct
          // slack elements for the leaves without worrying about conflicts with
          // the current members of this finite type.

          Node slack = nm->mkSkolem("slack", elementType);
          Node singleton = nm->mkNode(SINGLETON, slack);
          els.push_back(singleton);
          d_finite_type_slack_elements[elementType].push_back(slack);
          Trace("sets-model") << "Added slack element " << slack << " to set "
                              << eqc << std::endl;
        }
        else
        {
          els.push_back(
              nm->mkNode(SINGLETON, nm->mkSkolem("msde", elementType)));
        }
      }
    }
    else
    {
      Trace("sets-model") << "No slack elements for " << eqc << std::endl;
    }
  }
  else
  {
    Trace("sets-model") << "Build value for " << eqc
                        << " based on normal form, size = " << d_nf[eqc].size()
                        << std::endl;
    // it is union of venn regions
    for (unsigned j = 0; j < d_nf[eqc].size(); j++)
    {
      std::map<Node, Node>::const_iterator itm = mvals.find(d_nf[eqc][j]);
      if (itm != mvals.end())
      {
        els.push_back(itm->second);
      }
      else
      {
        Assert(false);
      }
    }
  }
}

void CardinalityExtension::collectFiniteTypeSetElements(TheoryModel* model)
{
  if (d_finite_type_constants_processed)
  {
    return;
  }
  for (const Node& set : getOrderedSetsEqClasses())
  {
    if (!set.getType().isInterpretedFinite())
    {
      continue;
    }
    if (!isModelValueBasic(set))
    {
      // only consider leaves in the cardinality graph
      continue;
    }
    for (const std::pair<const Node, Node>& pair : d_state.getMembers(set))
    {
      Node member = pair.first;
      Node modelRepresentative = model->getRepresentative(member);
      std::vector<Node>& elements = d_finite_type_elements[member.getType()];
      if (std::find(elements.begin(), elements.end(), modelRepresentative)
          == elements.end())
      {
        elements.push_back(modelRepresentative);
      }
    }
  }
  d_finite_type_constants_processed = true;
}

const std::vector<Node>& CardinalityExtension::getFiniteTypeMembers(
    TypeNode typeNode)
{
  return d_finite_type_elements[typeNode];
}

}  // namespace sets
}  // namespace theory
}  // namespace CVC4
