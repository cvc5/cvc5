/*********************                                                        */
/*! \file inst_strategy_e_matching.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of e matching instantiation strategies
 **/

#include "theory/quantifiers/ematching/inst_strategy_e_matching.h"

#include "theory/quantifiers/ematching/pattern_term_selector.h"
#include "theory/quantifiers/quant_relevance.h"
#include "theory/quantifiers_engine.h"
#include "util/random.h"

using namespace CVC4::kind;
using namespace CVC4::theory::inst;

namespace CVC4 {
namespace theory {
namespace quantifiers {

//priority levels :
//1 : user patterns (when user-pat!={resort,ignore}), auto-gen patterns (for non-user pattern quantifiers, or when user-pat={resort,ignore})
//2 : user patterns (when user-pat=resort), auto gen patterns (for user pattern quantifiers when user-pat=use)

// user-pat=interleave alternates between use and resort

struct sortQuantifiersForSymbol {
  QuantRelevance* d_quant_rel;
  std::map< Node, Node > d_op_map;
  bool operator() (Node i, Node j) {
    size_t nqfsi = d_quant_rel->getNumQuantifiersForSymbol(d_op_map[i]);
    size_t nqfsj = d_quant_rel->getNumQuantifiersForSymbol(d_op_map[j]);
    if( nqfsi<nqfsj ){
      return true;
    }else if( nqfsi>nqfsj ){
      return false;
    }
    return false;
  }
};

struct sortTriggers {
  bool operator() (Node i, Node j) {
    int32_t wi = TriggerTermInfo::getTriggerWeight(i);
    int32_t wj = TriggerTermInfo::getTriggerWeight(j);
    if( wi==wj ){
      return i<j;
    }
    return wi < wj;
  }
};

InstStrategyAutoGenTriggers::InstStrategyAutoGenTriggers(
    QuantifiersEngine* qe,
    QuantifiersState& qs,
    QuantifiersInferenceManager& qim,
    QuantRelevance* qr)
    : InstStrategy(qe, qs, qim), d_quant_rel(qr)
{
  //how to select trigger terms
  d_tr_strategy = options::triggerSelMode();
  //whether to select new triggers during the search
  if( options::incrementTriggers() ){
    d_regenerate_frequency = 3;
    d_regenerate = true;
  }else{
    d_regenerate_frequency = 1;
    d_regenerate = false;
  }
}

void InstStrategyAutoGenTriggers::processResetInstantiationRound( Theory::Effort effort ){
  Trace("inst-alg-debug") << "reset auto-gen triggers" << std::endl;
  //reset triggers
  for( unsigned r=0; r<2; r++ ){
    std::map<Node, std::map<inst::Trigger*, bool> >& agts =
        d_auto_gen_trigger[r];
    for (std::pair<const Node, std::map<inst::Trigger*, bool> >& agt : agts)
    {
      for (std::map<inst::Trigger*, bool>::iterator it = agt.second.begin();
           it != agt.second.end();
           ++it)
      {
        it->first->resetInstantiationRound();
        it->first->reset(Node::null());
      }
    }
  }
  d_processed_trigger.clear();
  Trace("inst-alg-debug") << "done reset auto-gen triggers" << std::endl;
}

InstStrategyStatus InstStrategyAutoGenTriggers::process(Node f,
                                                        Theory::Effort effort,
                                                        int e)
{
  options::UserPatMode upMode = d_quantEngine->getInstUserPatMode();
  if (hasUserPatterns(f) && upMode == options::UserPatMode::TRUST)
  {
    return InstStrategyStatus::STATUS_UNKNOWN;
  }
  int peffort = (hasUserPatterns(f) && upMode != options::UserPatMode::IGNORE
                 && upMode != options::UserPatMode::RESORT)
                    ? 2
                    : 1;
  if (e < peffort)
  {
    return InstStrategyStatus::STATUS_UNFINISHED;
  }
  Trace("inst-alg") << "-> Auto-gen instantiate " << f << "..." << std::endl;
  bool gen = false;
  if (e == peffort)
  {
    if (d_counter.find(f) == d_counter.end())
    {
      d_counter[f] = 0;
      gen = true;
    }else{
      d_counter[f]++;
      gen = d_regenerate && d_counter[f] % d_regenerate_frequency == 0;
    }
  }
  else
  {
    gen = true;
  }
  if (gen)
  {
    generateTriggers(f);
    if (d_counter[f] == 0 && d_auto_gen_trigger[0][f].empty()
        && d_auto_gen_trigger[1][f].empty() && f.getNumChildren() == 2)
    {
      Trace("trigger-warn") << "Could not find trigger for " << f << std::endl;
    }
  }
  if (options::triggerActiveSelMode() != options::TriggerActiveSelMode::ALL)
  {
    int max_score = -1;
    Trigger* max_trigger = nullptr;
    std::map<Trigger*, bool>& agt = d_auto_gen_trigger[0][f];
    for (std::map<Trigger*, bool>::iterator it = agt.begin(); it != agt.end();
         ++it)
    {
      Trigger* t = it->first;
      int score = t->getActiveScore();
      if (options::triggerActiveSelMode() == options::TriggerActiveSelMode::MIN)
      {
        if (score >= 0 && (score < max_score || max_score < 0))
        {
          max_score = score;
          max_trigger = t;
        }
      }
      else
      {
        if (score > max_score)
        {
          max_score = score;
          max_trigger = t;
        }
      }
      agt[t] = false;
    }
    if (max_trigger != nullptr)
    {
      agt[max_trigger] = true;
    }
  }

  bool hasInst = false;
  for (unsigned r = 0; r < 2; r++)
  {
    std::map<Trigger*, bool>& agt = d_auto_gen_trigger[r][f];
    for (std::map<Trigger*, bool>::iterator it = agt.begin(); it != agt.end();
         ++it)
    {
      Trigger* tr = it->first;
      if (tr == nullptr || !it->second)
      {
        // trigger is null or currently disabled
        continue;
      }
      if (d_processed_trigger[f].find(tr) != d_processed_trigger[f].end())
      {
        // trigger is already processed this round
        continue;
      }
      d_processed_trigger[f][tr] = true;
      Trace("process-trigger") << "  Process ";
      tr->debugPrint("process-trigger");
      Trace("process-trigger") << "..." << std::endl;
      unsigned numInst = tr->addInstantiations();
      hasInst = numInst > 0 || hasInst;
      Trace("process-trigger")
          << "  Done, numInst = " << numInst << "." << std::endl;
      d_quantEngine->d_statistics.d_instantiations_auto_gen += numInst;
      if (r == 1)
      {
        d_quantEngine->d_statistics.d_multi_trigger_instantiations += numInst;
      }
      if (d_qstate.isInConflict())
      {
        break;
      }
    }
    if (d_qstate.isInConflict() || (hasInst && options::multiTriggerPriority()))
    {
      break;
    }
  }
  return InstStrategyStatus::STATUS_UNKNOWN;
}

void InstStrategyAutoGenTriggers::generateTriggers( Node f ){
  Trace("auto-gen-trigger-debug") << "Generate triggers for " << f << ", #var=" << f[0].getNumChildren() << "..." << std::endl;

  // first, generate the set of pattern terms
  if (!generatePatternTerms(f))
  {
    Trace("auto-gen-trigger-debug")
        << "...failed to generate pattern terms" << std::endl;
    return;
  }

  // then, group them to make triggers
  unsigned rmin = d_patTerms[0][f].empty() ? 1 : 0;
  unsigned rmax = options::multiTriggerWhenSingle() ? 1 : rmin;
  for (unsigned r = rmin; r <= rmax; r++)
  {
    std::vector<Node> patTerms;
    std::vector<Node>& ptc = d_patTerms[r][f];
    for (const Node& p : ptc)
    {
      if (r == 1 || d_single_trigger_gen.find(p) == d_single_trigger_gen.end())
      {
        patTerms.push_back(p);
      }
    }
    if (patTerms.empty())
    {
      continue;
    }
    Trace("auto-gen-trigger") << "Generate trigger for " << f << std::endl;
    // sort terms based on relevance
    if (options::relevantTriggers())
    {
      Assert(d_quant_rel);
      sortQuantifiersForSymbol sqfs;
      sqfs.d_quant_rel = d_quant_rel;
      for (const Node& p : patTerms)
      {
        Assert(d_pat_to_mpat.find(p) != d_pat_to_mpat.end());
        Assert(d_pat_to_mpat[p].hasOperator());
        sqfs.d_op_map[p] = d_pat_to_mpat[p].getOperator();
      }
      // sort based on # occurrences (this will cause Trigger to select rarer
      // symbols)
      std::sort(patTerms.begin(), patTerms.end(), sqfs);
      if (Debug.isOn("relevant-trigger"))
      {
        Debug("relevant-trigger") << "Terms based on relevance: " << std::endl;
        for (const Node& p : patTerms)
        {
          Debug("relevant-trigger")
              << "   " << p << " from " << d_pat_to_mpat[p] << " (";
          Debug("relevant-trigger") << d_quant_rel->getNumQuantifiersForSymbol(
                                           d_pat_to_mpat[p].getOperator())
                                    << ")" << std::endl;
        }
      }
    }
    // now, generate the trigger...
    Trigger* tr = NULL;
    if (d_is_single_trigger[patTerms[0]])
    {
      tr = Trigger::mkTrigger(d_quantEngine,
                              d_qim,
                              f,
                              patTerms[0],
                              false,
                              Trigger::TR_RETURN_NULL,
                              d_num_trigger_vars[f]);
      d_single_trigger_gen[patTerms[0]] = true;
    }
    else
    {
      // only generate multi trigger if option set, or if no single triggers
      // exist
      if (!d_patTerms[0][f].empty())
      {
        if (options::multiTriggerWhenSingle())
        {
          Trace("multi-trigger-debug")
              << "Resort to choosing multi-triggers..." << std::endl;
        }
        else
        {
          return;
        }
      }
      // if we are re-generating triggers, shuffle based on some method
      if (d_made_multi_trigger[f])
      {
        std::shuffle(patTerms.begin(),
                     patTerms.end(),
                     Random::getRandom());  // shuffle randomly
      }
      else
      {
        d_made_multi_trigger[f] = true;
      }
      // will possibly want to get an old trigger
      tr = Trigger::mkTrigger(d_quantEngine,
                              d_qim,
                              f,
                              patTerms,
                              false,
                              Trigger::TR_GET_OLD,
                              d_num_trigger_vars[f]);
    }
    if (tr == nullptr)
    {
      // did not generate a trigger
      continue;
    }
    addTrigger(tr, f);
    if (tr->isMultiTrigger())
    {
      // only add a single multi-trigger
      continue;
    }
    // if we are generating additional triggers...
    size_t index = 0;
    if (index < patTerms.size())
    {
      // check if similar patterns exist, and if so, add them additionally
      unsigned nqfs_curr = 0;
      if (options::relevantTriggers())
      {
        nqfs_curr =
            d_quant_rel->getNumQuantifiersForSymbol(patTerms[0].getOperator());
      }
      index++;
      bool success = true;
      while (success && index < patTerms.size()
             && d_is_single_trigger[patTerms[index]])
      {
        success = false;
        if (!options::relevantTriggers()
            || d_quant_rel->getNumQuantifiersForSymbol(
                   patTerms[index].getOperator())
                   <= nqfs_curr)
        {
          d_single_trigger_gen[patTerms[index]] = true;
          Trigger* tr2 = Trigger::mkTrigger(d_quantEngine,
                                            d_qim,
                                            f,
                                            patTerms[index],
                                            false,
                                            Trigger::TR_RETURN_NULL,
                                            d_num_trigger_vars[f]);
          addTrigger(tr2, f);
          success = true;
        }
        index++;
      }
    }
  }
}

bool InstStrategyAutoGenTriggers::generatePatternTerms(Node f)
{
  if (d_patTerms[0].find(f) != d_patTerms[0].end())
  {
    // already generated
    return true;
  }
  // determine all possible pattern terms based on trigger term selection
  // strategy d_tr_strategy
  d_patTerms[0][f].clear();
  d_patTerms[1][f].clear();
  bool ntrivTriggers = options::relationalTriggers();
  std::vector<Node> patTermsF;
  std::map<Node, inst::TriggerTermInfo> tinfo;
  TermUtil* tu = d_quantEngine->getTermUtil();
  NodeManager* nm = NodeManager::currentNM();
  // well-defined function: can assume LHS is only pattern
  if (options::quantFunWellDefined())
  {
    Node hd = QuantAttributes::getFunDefHead(f);
    if (!hd.isNull())
    {
      hd = tu->substituteBoundVariablesToInstConstants(hd, f);
      patTermsF.push_back(hd);
      tinfo[hd].init(f, hd);
    }
  }
  // otherwise, use algorithm for collecting pattern terms
  if (patTermsF.empty())
  {
    Node bd = tu->getInstConstantBody(f);
    PatternTermSelector pts(f, d_tr_strategy, d_user_no_gen[f], true);
    pts.collect(bd, patTermsF, tinfo);
    if (ntrivTriggers)
    {
      sortTriggers st;
      std::sort(patTermsF.begin(), patTermsF.end(), st);
    }
    if (Trace.isOn("auto-gen-trigger-debug"))
    {
      Trace("auto-gen-trigger-debug")
          << "Collected pat terms for " << bd
          << ", no-patterns : " << d_user_no_gen[f].size() << std::endl;
      for (const Node& p : patTermsF)
      {
        Assert(tinfo.find(p) != tinfo.end());
        Trace("auto-gen-trigger-debug") << "   " << p << std::endl;
        Trace("auto-gen-trigger-debug2")
            << "     info = [" << tinfo[p].d_reqPol << ", "
            << tinfo[p].d_reqPolEq << ", " << tinfo[p].d_fv.size() << "]"
            << std::endl;
      }
      Trace("auto-gen-trigger-debug") << std::endl;
    }
  }
  // sort into single/multi triggers, calculate which terms should not be
  // considered
  std::map<Node, bool> vcMap;
  std::map<Node, bool> rmPatTermsF;
  int32_t last_weight = -1;
  for (const Node& p : patTermsF)
  {
    Assert(p.getKind() != NOT);
    bool newVar = false;
    inst::TriggerTermInfo& tip = tinfo[p];
    for (const Node& v : tip.d_fv)
    {
      if (vcMap.find(v) == vcMap.end())
      {
        vcMap[v] = true;
        newVar = true;
      }
    }
    int32_t curr_w = TriggerTermInfo::getTriggerWeight(p);
    // triggers whose value is maximum (2) are considered expendable.
    if (ntrivTriggers && !newVar && last_weight != -1 && curr_w > last_weight
        && curr_w >= 2)
    {
      Trace("auto-gen-trigger-debug")
          << "...exclude expendible non-trivial trigger : " << p << std::endl;
      rmPatTermsF[p] = true;
    }
    else
    {
      last_weight = curr_w;
    }
  }
  d_num_trigger_vars[f] = vcMap.size();
  if (d_num_trigger_vars[f] > 0
      && d_num_trigger_vars[f] < f[0].getNumChildren())
  {
    Trace("auto-gen-trigger-partial")
        << "Quantified formula : " << f << std::endl;
    Trace("auto-gen-trigger-partial")
        << "...does not contain all variables in triggers!!!" << std::endl;
    // Invoke partial trigger strategy: partition variables of quantified
    // formula into (X,Y) where X are contained in a trigger and Y are not.
    // We then force a split of the quantified formula so that it becomes:
    //   forall X. forall Y. P( X, Y )
    // and hence is treatable by E-matching. We only do this for "standard"
    // quantified formulas (those with only two children), since this
    // technique should not be used for e.g. quantifiers marked for
    // quantifier elimination.
    QAttributes qa;
    QuantAttributes::computeQuantAttributes(f, qa);
    if (options::partialTriggers() && qa.isStandard())
    {
      std::vector<Node> vcs[2];
      for (size_t i = 0, nchild = f[0].getNumChildren(); i < nchild; i++)
      {
        Node ic = tu->getInstantiationConstant(f, i);
        vcs[vcMap.find(ic) == vcMap.end() ? 0 : 1].push_back(f[0][i]);
      }
      for (size_t i = 0; i < 2; i++)
      {
        d_vc_partition[i][f] = nm->mkNode(BOUND_VAR_LIST, vcs[i]);
      }
    }
    else
    {
      return false;
    }
  }
  for (const Node& patf : patTermsF)
  {
    Node pat = patf;
    if (rmPatTermsF.find(pat) != rmPatTermsF.end())
    {
      continue;
    }
    Trace("auto-gen-trigger-debug")
        << "...processing pattern " << pat << std::endl;
    Node mpat = pat;
    // process the pattern: if it has a required polarity, consider it
    Assert(tinfo.find(pat) != tinfo.end());
    int rpol = tinfo[pat].d_reqPol;
    Node rpoleq = tinfo[pat].d_reqPolEq;
    size_t num_fv = tinfo[pat].d_fv.size();
    Trace("auto-gen-trigger-debug")
        << "...required polarity for " << pat << " is " << rpol
        << ", eq=" << rpoleq << std::endl;
    if (rpol != 0)
    {
      Assert(rpol == 1 || rpol == -1);
      if (TriggerTermInfo::isRelationalTrigger(pat))
      {
        pat = rpol == -1 ? pat.negate() : pat;
      }
      else
      {
        Assert(TriggerTermInfo::isAtomicTrigger(pat));
        if (pat.getType().isBoolean() && rpoleq.isNull())
        {
          if (options::literalMatchMode() == options::LiteralMatchMode::USE)
          {
            pat = pat.eqNode(nm->mkConst(rpol == -1)).negate();
          }
          else if (options::literalMatchMode()
                   != options::LiteralMatchMode::NONE)
          {
            pat = pat.eqNode(nm->mkConst(rpol == 1));
          }
        }
        else
        {
          Assert(!rpoleq.isNull());
          if (rpol == -1)
          {
            if (options::literalMatchMode() != options::LiteralMatchMode::NONE)
            {
              // all equivalence classes except rpoleq
              pat = pat.eqNode(rpoleq).negate();
            }
          }
          else if (rpol == 1)
          {
            if (options::literalMatchMode() == options::LiteralMatchMode::AGG)
            {
              // only equivalence class rpoleq
              pat = pat.eqNode(rpoleq);
            }
          }
        }
      }
      Trace("auto-gen-trigger-debug") << "...got : " << pat << std::endl;
    }
    else
    {
      if (TriggerTermInfo::isRelationalTrigger(pat))
      {
        // consider both polarities
        addPatternToPool(f, pat.negate(), num_fv, mpat);
      }
    }
    addPatternToPool(f, pat, num_fv, mpat);
  }
  // tinfo not used below this point
  d_made_multi_trigger[f] = false;
  if (Trace.isOn("auto-gen-trigger"))
  {
    Trace("auto-gen-trigger")
        << "Single trigger pool for " << f << " : " << std::endl;
    std::vector<Node>& spats = d_patTerms[0][f];
    for (size_t i = 0, psize = spats.size(); i < psize; i++)
    {
      Trace("auto-gen-trigger") << "   " << spats[i] << std::endl;
    }
    std::vector<Node>& mpats = d_patTerms[0][f];
    if (!mpats.empty())
    {
      Trace("auto-gen-trigger")
          << "Multi-trigger term pool for " << f << " : " << std::endl;
      for (size_t i = 0, psize = mpats.size(); i < psize; i++)
      {
        Trace("auto-gen-trigger") << "   " << mpats[i] << std::endl;
      }
    }
  }
  return true;
}

void InstStrategyAutoGenTriggers::addPatternToPool( Node q, Node pat, unsigned num_fv, Node mpat ) {
  d_pat_to_mpat[pat] = mpat;
  unsigned num_vars = options::partialTriggers() ? d_num_trigger_vars[q] : q[0].getNumChildren();
  if (num_fv == num_vars)
  {
    d_patTerms[0][q].push_back( pat );
    d_is_single_trigger[ pat ] = true;
  }else{
    d_patTerms[1][q].push_back( pat );
    d_is_single_trigger[ pat ] = false;
  }
}


void InstStrategyAutoGenTriggers::addTrigger( inst::Trigger * tr, Node q ) {
  if (tr == nullptr)
  {
    return;
  }
  if (d_num_trigger_vars[q] < q[0].getNumChildren())
  {
    NodeManager* nm = NodeManager::currentNM();
    // partial trigger : generate implication to mark user pattern
    Node pat =
        d_quantEngine->getTermUtil()->substituteInstConstantsToBoundVariables(
            tr->getInstPattern(), q);
    Node ipl = nm->mkNode(INST_PATTERN_LIST, pat);
    Node qq = nm->mkNode(FORALL,
                         d_vc_partition[1][q],
                         nm->mkNode(FORALL, d_vc_partition[0][q], q[1]),
                         ipl);
    Trace("auto-gen-trigger-partial")
        << "Make partially specified user pattern: " << std::endl;
    Trace("auto-gen-trigger-partial") << "  " << qq << std::endl;
    Node lem = nm->mkNode(OR, q.negate(), qq);
    d_qim.addPendingLemma(lem);
    return;
  }
  unsigned tindex;
  if (tr->isMultiTrigger())
  {
    // disable all other multi triggers
    std::map<Trigger*, bool>& agt = d_auto_gen_trigger[1][q];
    for (std::map<Trigger*, bool>::iterator it = agt.begin(); it != agt.end();
         ++it)
    {
      agt[it->first] = false;
    }
    tindex = 1;
  }
  else
  {
    tindex = 0;
  }
  // making it during an instantiation round, so must reset
  std::map<Trigger*, bool>& agt = d_auto_gen_trigger[tindex][q];
  if (agt.find(tr) == agt.end())
  {
    tr->resetInstantiationRound();
    tr->reset(Node::null());
  }
  agt[tr] = true;
}

bool InstStrategyAutoGenTriggers::hasUserPatterns( Node q ) {
  if (q.getNumChildren() != 3)
  {
    return false;
  }
  std::map<Node, bool>::iterator it = d_hasUserPatterns.find(q);
  if (it != d_hasUserPatterns.end())
  {
    return it->second;
  }
  bool hasPat = false;
  for (const Node& ip : q[2])
  {
    if (ip.getKind() == INST_PATTERN)
    {
      hasPat = true;
      break;
    }
  }
  d_hasUserPatterns[q] = hasPat;
  return hasPat;
}

void InstStrategyAutoGenTriggers::addUserNoPattern( Node q, Node pat ) {
  Assert(pat.getKind() == INST_NO_PATTERN && pat.getNumChildren() == 1);
  std::vector<Node>& ung = d_user_no_gen[q];
  if (std::find(ung.begin(), ung.end(), pat[0]) == ung.end())
  {
    Trace("user-pat") << "Add user no-pattern: " << pat[0] << " for " << q << std::endl;
    ung.push_back(pat[0]);
  }
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
