/*********************                                                        */
/*! \file sygus_unif_rl.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_unif_rl
 **/

#include "theory/quantifiers/sygus/sygus_unif_rl.h"

#include "theory/quantifiers/sygus/ce_guided_conjecture.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusUnifRl::SygusUnifRl(CegConjecture* p) : d_parent(p) {}
SygusUnifRl::~SygusUnifRl() {}
void SygusUnifRl::initialize(QuantifiersEngine* qe,
                             const std::vector<Node>& funs,
                             std::vector<Node>& enums,
                             std::vector<Node>& lemmas)
{
  d_ecache.clear();
  d_cand_to_pt_enum.clear();
  // initialize
  std::vector<Node> all_enums;
  SygusUnif::initialize(qe, funs, all_enums, lemmas);
  // based on the strategy inferred for each function, determine if we are
  // using a unification strategy that is compatible our approach.
  for (const Node& f : funs)
  {
    registerStrategy(f);
  }
  enums.insert(enums.end(), d_cond_enums.begin(), d_cond_enums.end());
  /* Copy candidates and check whether CegisUnif for any of them */
  for (const Node& c : d_unif_candidates)
  {
    d_app_to_pt[c].clear();
    d_cand_to_pt_enum[c].clear();
    d_purified_count[c] = 0;
  }
}

void SygusUnifRl::notifyEnumeration(Node e, Node v, std::vector<Node>& lemmas)
{
  Trace("sygus-unif-rl-notify") << "SyGuSUnifRl: Adding to enum " << e
                                << " value " << v << "\n";
  d_ecache[e].d_enum_vals.push_back(v);
  /* Exclude v from next enumerations for e */
  Node exc_lemma =
      d_tds->getExplain()->getExplanationForEquality(e, v).negate();
  Trace("sygus-unif-rl-notify")
      << "SygusUnifRl : enumeration exclude lemma : " << exc_lemma << std::endl;
  lemmas.push_back(exc_lemma);
}

Node SygusUnifRl::purifyLemma(Node n,
                              bool ensureConst,
                              std::vector<Node>& model_guards,
                              BoolNodePairMap& cache)
{
  Trace("sygus-unif-rl-purify") << "PurifyLemma : " << n << "\n";
  BoolNodePairMap::const_iterator it = cache.find(BoolNodePair(ensureConst, n));
  if (it != cache.end())
  {
    Trace("sygus-unif-rl-purify-debug") << "... already visited " << n << "\n";
    return it->second;
  }
  /* Recurse */
  unsigned size = n.getNumChildren();
  Kind k = n.getKind();
  /* We retrive model value now because purified node may not have a value */
  Node nv = n;
  /* Whether application of a function-to-synthesize */
  bool fapp = k == APPLY_UF && size > 0;
  bool u_fapp = false;
  bool nu_fapp = false;
  if (fapp)
  {
    Assert(std::find(d_candidates.begin(), d_candidates.end(), n[0])
           != d_candidates.end());
    /* Whether application of a (non-)unification function-to-synthesize */
    u_fapp = usingUnif(n[0]);
    nu_fapp = !usingUnif(n[0]);
    /* get model value of non-top level applications of functions-to-synthesize
      occurring under a unification function-to-synthesize */
    if (ensureConst)
    {
      nv = d_parent->getModelValue(n);
      Assert(n != nv);
      Trace("sygus-unif-rl-purify")
          << "PurifyLemma : model value for " << n << " is " << nv << "\n";
    }
  }
  /* Travese to purify */
  bool childChanged = false;
  std::vector<Node> children;
  NodeManager* nm = NodeManager::currentNM();
  for (unsigned i = 0; i < size; ++i)
  {
    if (i == 0 && fapp)
    {
      children.push_back(n[i]);
      continue;
    }
    /* Arguments of non-unif functions do not need to be constant */
    Node child = purifyLemma(
        n[i], !nu_fapp && (ensureConst || u_fapp), model_guards, cache);
    children.push_back(child);
    childChanged = childChanged || child != n[i];
  }
  Node nb;
  if (childChanged)
  {
    if (n.hasOperator())
    {
      children.insert(children.begin(), n.getOperator());
    }
    nb = NodeManager::currentNM()->mkNode(k, children);
    Trace("sygus-unif-rl-purify") << "PurifyLemma : transformed " << n
                                  << " into " << nb << "\n";
  }
  else
  {
    nb = n;
  }
  /* Map to point enumerator every unification function-to-synthesize  */
  if (u_fapp)
  {
    Node np;
    std::map<Node, Node>::const_iterator it = d_app_to_purified.find(nb);
    if (it == d_app_to_purified.end())
    {
      if (!childChanged)
      {
        Assert(nb.hasOperator());
        children.insert(children.begin(), n.getOperator());
      }
      /* Build purified head with fresh skolem and recreate node */
      std::stringstream ss;
      ss << nb[0] << "_" << d_purified_count[nb[0]]++;
      Node new_f = nm->mkSkolem(ss.str(), nb[0].getType());
      /* Adds new enumerator to map from candidate */
      Trace("sygus-unif-rl-purify") << "...new enum " << new_f
                                        << " for candidate " << nb[0] << "\n";
      d_cand_to_pt_enum[nb[0]].push_back(new_f);
      /* Maps new enumerator to its respective tuple of arguments */
      d_app_to_pt[new_f] =
          std::vector<Node>(children.begin() + 2, children.end());
      if (Trace.isOn("sygus-unif-rl-purify"))
      {
        Trace("sygus-unif-rl-purify") << "...[" << new_f << "] --> (";
        for (const Node& pt_i : d_app_to_pt[new_f])
        {
          Trace("sygus-unif-rl-purify") << pt_i << " ";
        }
        Trace("sygus-unif-rl-purify") << ")\n";
      }
      /* replace first child and rebulid node */
      children[1] = new_f;
      np = NodeManager::currentNM()->mkNode(k, children);
      d_app_to_purified[nb] = np;
    }
    else
    {
      np = it->second;
    }
    Trace("sygus-unif-rl-purify")
        << "PurifyLemma : purified head and transformed " << nb << " into "
        << np << "\n";
    nb = np;
  }
  /* Add equality between purified fapp and model value */
  if (ensureConst && fapp)
  {
    model_guards.push_back(
        NodeManager::currentNM()->mkNode(EQUAL, nv, nb).negate());
    nb = nv;
    Trace("sygus-unif-rl-purify") << "PurifyLemma : adding model eq "
                                  << model_guards.back() << "\n";
  }
  nb = Rewriter::rewrite(nb);
  /* every non-top level application of function-to-synthesize must be reduced
     to a concrete constant */
  Assert(!ensureConst || nb.isConst());
  Trace("sygus-unif-rl-purify-debug") << "... caching [" << n << "] = " << nb
                                      << "\n";
  cache[BoolNodePair(ensureConst, n)] = nb;
  return nb;
}

Node SygusUnifRl::addRefLemma(Node lemma, std::map< Node, std::vector< Node > >& new_eval_pts)
{
  Trace("sygus-unif-rl-purify") << "Registering lemma at SygusUnif : " << lemma
                               << "\n";
  std::vector<Node> model_guards;
  BoolNodePairMap cache;
  // cache previous sizes
  std::map< Node, unsigned > prev_n_eval_pts;
  for( const std::pair<const Node, std::vector<Node>>& cp : d_cand_to_pt_enum )
  {
    prev_n_eval_pts[cp.first] = cp.second.size();
  }
  
  /* Make the purified lemma which will guide the unification utility. */
  Node plem = purifyLemma(lemma, false, model_guards, cache);
  if (!model_guards.empty())
  {
    model_guards.push_back(plem);
    plem = NodeManager::currentNM()->mkNode(OR, model_guards);
  }
  plem = Rewriter::rewrite(plem);
  Trace("sygus-unif-rl-purify") << "Purified lemma : " << plem << "\n";
  
  Trace("sygus-unif-rl-purify") << "Collect new evaluation points...\n";
  for( const std::pair<const Node, std::vector<Node>>& cp : d_cand_to_pt_enum )
  {
    Node c = cp.first;
    unsigned prevn = 0;
    std::map< Node, unsigned >::iterator itp = prev_n_eval_pts.find(c);
    if( itp!=prev_n_eval_pts.end() )
    {
      prevn = itp->second;
    }
    for( unsigned j=prevn, size = cp.second.size(); j<size; j++ )
    {
      new_eval_pts[c].push_back( cp.second[j] );
    }
  }
  
  return plem;
}

void SygusUnifRl::initializeConstructSol() {}
void SygusUnifRl::initializeConstructSolFor(Node f) {}
bool SygusUnifRl::constructSolution(std::vector<Node>& sols)
{
  initializeConstructSol();
  for (const Node& c : d_candidates)
  {
    if (!usingUnif(c))
    {
      Node v = d_parent->getModelValue(c);
      Trace("sygus-unif-rl-sol") << "Adding solution " << v
                                 << " to non-unif candidate " << c << "\n";
      sols.push_back(v);
    }
    else
    {
      initializeConstructSolFor(c);
      Node v =
          constructSol(c, d_strategy[c].getRootEnumerator(), role_equal, 0);
      if (v.isNull())
      {
        return false;
      }
      Trace("sygus-unif-rl-sol")
          << "Adding solution " << v << " to unif candidate " << c << "\n";
      sols.push_back(v);
    }
  }
  return true;
}

Node SygusUnifRl::constructSol(Node f, Node e, NodeRole nrole, int ind)
{
  indent("sygus-unif-sol", ind);
  Trace("sygus-unif-sol") << "ConstructSol: SygusRL : " << e << std::endl;
  // is there a decision tree strategy?
  if (nrole == role_equal)
  {
    std::map<Node, DecisionTreeInfo>::iterator itd = d_enum_to_dt.find(e);
    if (itd != d_enum_to_dt.end())
    {
      indent("sygus-unif-sol", ind);
      Trace("sygus-unif-sol")
          << "...it has a decision tree strategy." << std::endl;
    }
  }

  return Node::null();
}

bool SygusUnifRl::usingUnif(Node f)
{
  return d_unif_candidates.find(f) != d_unif_candidates.end();
}

void SygusUnifRl::registerStrategy(Node f)
{
  if (Trace.isOn("sygus-unif-rl-strat"))
  {
    Trace("sygus-unif-rl-strat")
        << "Strategy for " << f << " is : " << std::endl;
    d_strategy[f].debugPrint("sygus-unif-rl-strat");
  }
  Trace("sygus-unif-rl-strat") << "Register..." << std::endl;
  Node e = d_strategy[f].getRootEnumerator();
  std::map<Node, std::map<NodeRole, bool> > visited;
  registerStrategyNode(f, e, role_equal, visited);
}

void SygusUnifRl::registerStrategyNode(
    Node f,
    Node e,
    NodeRole nrole,
    std::map<Node, std::map<NodeRole, bool> >& visited)
{
  Trace("sygus-unif-rl-strat") << "  register node " << e << std::endl;
  if (visited[e].find(nrole) != visited[e].end())
  {
    return;
  }
  visited[e][nrole] = true;
  TypeNode etn = e.getType();
  EnumTypeInfo& tinfo = d_strategy[f].getEnumTypeInfo(etn);
  StrategyNode& snode = tinfo.getStrategyNode(nrole);
  for (unsigned j = 0, size = snode.d_strats.size(); j < size; j++)
  {
    EnumTypeInfoStrat* etis = snode.d_strats[j];
    StrategyType strat = etis->d_this;
    // is this a simple recursive ITE strategy?
    if (strat == strat_ITE && nrole == role_equal)
    {
      bool success = true;
      for (unsigned c = 1; c <= 2; c++)
      {
        std::pair<Node, NodeRole> child = etis->d_cenum[c];
        if (child.first != e || child.second != nrole)
        {
          success = false;
          break;
        }
      }
      if (success)
      {
        Node cond = etis->d_cenum[0].first;
        Assert(etis->d_cenum[0].second == role_ite_condition);
        Trace("sygus-unif-rl-strat")
            << "  ...detected recursive ITE strategy, condition enumerator : "
            << cond << std::endl;
        // indicate that we will be enumerating values for cond
        registerConditionalEnumerator(f, e, cond);
      }
    }
    // TODO: recurse? for (std::pair<Node, NodeRole>& cec : etis->d_cenum)
  }
}

void SygusUnifRl::registerConditionalEnumerator(Node f, Node e, Node cond)
{
  // we will do unification for this candidate
  d_unif_candidates.insert(f);
  // add to the list of all conditional enumerators
  if (std::find(d_cond_enums.begin(), d_cond_enums.end(), cond)
      == d_cond_enums.end())
  {
    d_cond_enums.push_back(cond);
    // register the conditional enumerator
    d_tds->registerEnumerator(cond, f, d_parent, true);
  }
  // register that this enumerator has a decision tree construction
  d_enum_to_dt[e].d_cond_enum = cond;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
