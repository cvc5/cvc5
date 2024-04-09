/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Model-based quantifier instantiation
 */

#include "theory/quantifiers/mbqi_sygus_enum.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "printer/smt2/smt2_printer.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/inst_strategy_mbqi.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "theory/smt_engine_subsolver.h"
#include "util/random.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

void MVarInfo::initialize(Env& env,
                          InstStrategyMbqi& parent,
                          const Node& q,
                          const Node& v,
                          const std::vector<Node>& etrules)
{
  NodeManager* nm = NodeManager::currentNM();
  TypeNode tn = v.getType();
  Assert(MQuantInfo::shouldEnumerate(tn));
  TypeNode retType = tn;
  std::vector<Node> trules;
  if (tn.isFunction())
  {
    std::vector<TypeNode> argTypes = tn.getArgTypes();
    retType = tn.getRangeType();
    std::vector<Node> vs;
    for (const TypeNode& tnc : argTypes)
    {
      Node vc = nm->mkBoundVar(tnc);
      vs.push_back(vc);
    }
    d_lamVars = nm->mkNode(Kind::BOUND_VAR_LIST, vs);
    trules.insert(trules.end(), vs.begin(), vs.end());
  }
  // NOTE: get free symbols from body of quantified formula here??
  std::unordered_set<Node> syms;
  expr::getSymbols(q[1], syms);
  trules.insert(trules.end(), syms.begin(), syms.end());
  // include the external terminal rules
  trules.insert(trules.end(), etrules.begin(), etrules.end());
  // add extra symbols to grammar
  for (const auto& symbol : parent.getGlobalSyms()) {
    if (std::find(trules.begin(), trules.end(), symbol) == trules.end()) {
        trules.push_back(symbol);
    }
  }
  Trace("mbqi-model-enum") << "Symbols: " << trules << std::endl;
  // TODO: could add more symbols to trules to improve the enumerated terms
  SygusGrammarCons sgc;
  Node bvl;
  TypeNode tng = sgc.mkDefaultSygusType(env, retType, bvl, trules);
  if (TraceIsOn("mbqi-model-enum"))
  {
    Trace("mbqi-model-enum") << "Enumerate terms for " << retType;
    if (!d_lamVars.isNull())
    {
      Trace("mbqi-model-enum") << ", variable list " << d_lamVars;
    }
    Trace("mbqi-model-enum") << std::endl;
    Trace("mbqi-model-enum") << "Based on grammar:" << std::endl;
    Trace("mbqi-model-enum")
        << printer::smt2::Smt2Printer::sygusGrammarString(tng) << std::endl;
  }
  d_senum.reset(new SygusTermEnumerator(env, tng));
}

Node MVarInfo::getEnumeratedTerm(size_t i)
{
  NodeManager* nm = NodeManager::currentNM();
  size_t nullCount = 0;
  while (i >= d_enum.size())
  {
    Node curr = d_senum->getCurrent();
    Trace("mbqi-sygus-enum") << "Enumerate: " << curr << std::endl;
    if (!curr.isNull())
    {
      if (!d_lamVars.isNull())
      {
        curr = nm->mkNode(Kind::LAMBDA, d_lamVars, curr);
      }
      d_enum.push_back(curr);
      nullCount = 0;
    }
    else
    {
      nullCount++;
      if (nullCount > 100)
      {
        // break if we aren't making progress
        break;
      }
    }
    if (!d_senum->incrementPartial())
    {
      // enumeration is finished
      break;
    }
  }
  if (i >= d_enum.size())
  {
    return Node::null();
  }
  return d_enum[i];
}

void MQuantInfo::initialize(Env& env, InstStrategyMbqi& d_parent, const Node& q)
{
  // TODO: external terminal rules? maybe pass all symbols to this?
  std::vector<Node> etrules;
  for (const Node& v : q[0])
  {
    size_t index = d_vinfo.size();
    d_vinfo.emplace_back();
    TypeNode vtn = v.getType();
    // if enumerated, add to list
    if (shouldEnumerate(vtn))
    {
      d_indices.push_back(index);
    }
    else
    {
      d_nindices.push_back(index);
      // variables defined in terms of others
      etrules.push_back(v);
    }
  }
  // initialize the variables we are instantiating
  for (size_t index : d_indices)
  {
    d_vinfo[index].initialize(env, d_parent, q, q[0][index], etrules);
  }
}

MVarInfo& MQuantInfo::getVarInfo(size_t index)
{
  Assert(index < d_vinfo.size());
  return d_vinfo[index];
}

std::vector<size_t> MQuantInfo::getInstIndicies() { return d_indices; }
std::vector<size_t> MQuantInfo::getNoInstIndicies() { return d_nindices; }

bool MQuantInfo::shouldEnumerate(const TypeNode& tn)
{
  if (tn.isUninterpretedSort())
  {
    return false;
  }
  return true;
}

MbqiFastSygus::MbqiFastSygus(Env& env, InstStrategyMbqi& parent)
    : EnvObj(env), d_parent(parent)
{
}

MQuantInfo& MbqiFastSygus::getOrMkQuantInfo(const Node& q)
{
  std::map<Node, MQuantInfo>::iterator it = d_qinfo.find(q);
  if (it == d_qinfo.end())
  {
    MQuantInfo& qi = d_qinfo[q];
    qi.initialize(d_env, d_parent, q);
    return qi;
  }
  return it->second;
}

bool MbqiFastSygus::constructInstantiation(
    const Node& q,
    const Node& query,
    const std::vector<Node>& vars,
    std::vector<Node>& mvs,
    const std::map<Node, Node>& mvFreshVar)
{
  // TODO: it would better for the last child to simply invoke addInstantiation
  // as an oracle to determine if the instantiation is feasiable. This would
  // avoid one subsolver call per instantiation we construct.
  // Doing this ignores the constructed model in favor of using "entailment"
  // from the main solver. This is likely a better notion of filtering.
  Assert(q[0].getNumChildren() == vars.size());
  Assert(vars.size() == mvs.size());
  if (TraceIsOn("mbqi-model-enum"))
  {
    Trace("mbqi-model-enum") << "Instantiate " << q << std::endl;
    for (size_t i = 0, nvars = vars.size(); i < nvars; i++)
    {
      Trace("mbqi-model-enum")
          << "  " << q[0][i] << " -> " << mvs[i] << std::endl;
    }
  }
  MQuantInfo& qi = getOrMkQuantInfo(q);
  std::vector<size_t> indices = qi.getInstIndicies();
  std::vector<size_t> nindices = qi.getNoInstIndicies();
  Subs inst;
  Subs vinst;
  std::unordered_map<Node, Node> tmpCMap;
  for (size_t i : nindices)
  {
    Node v = mvs[i];
    v = d_parent.convertFromModel(v, tmpCMap, mvFreshVar);
    if (v.isNull())
    {
      return false;
    }
    Trace("mbqi-model-enum")
        << "* Assume: " << q[0][i] << " -> " << v << std::endl;
    // if we don't enumerate it, we are already considering this instantiation
    inst.add(vars[i], v);
    vinst.add(q[0][i], v);
  }
  Node queryCurr = query;
  Trace("mbqi-model-enum") << "...query is " << queryCurr << std::endl;
  queryCurr = rewrite(inst.apply(queryCurr));
  Trace("mbqi-model-enum") << "...processed is " << queryCurr << std::endl;
  std::shuffle(indices.begin(), indices.end(), Random::getRandom());
  for (size_t i = 0, isize = indices.size(); i < isize; i++)
  {
    size_t ii = indices[i];
    TNode v = vars[ii];
    MVarInfo& vi = qi.getVarInfo(ii);
    size_t cindex = 0;
    bool success = false;
    bool successEnum;
    do
    {
      Node ret = vi.getEnumeratedTerm(cindex);
      cindex++;
      Node retc;
      if (!ret.isNull())
      {
        Trace("mbqi-model-enum") << "- Try candidate: " << ret << std::endl;
        // apply current substitution (to account for cases where ret has
        // other variables in its grammar).
        ret = vinst.apply(ret);
        retc = ret;
        successEnum = true;
        // now convert the value
        std::unordered_map<Node, Node> tmpConvertMap;
        std::map<TypeNode, std::unordered_set<Node> > freshVarType;
        retc = d_parent.convertToQuery(retc, tmpConvertMap, freshVarType);
      }
      else
      {
        Trace("mbqi-model-enum")
            << "- Failed to enumerate candidate" << std::endl;
        // if we failed to enumerate, just try the original
        Node mc = d_parent.convertFromModel(mvs[ii], tmpCMap, mvFreshVar);
        if (mc.isNull())
        {
          // if failed to convert, we fail
          return false;
        }
        ret = mc;
        retc = mc;
        successEnum = false;
      }
      Trace("mbqi-model-enum")
          << "- Converted candidate: " << v << " -> " << retc << std::endl;
      // see if it is still satisfiable, if still SAT, we replace
      Node queryCheck = queryCurr.substitute(v, TNode(retc));
      queryCheck = rewrite(queryCheck);
      Trace("mbqi-model-enum") << "...check " << queryCheck << std::endl;
      // since we may have free constants from the grammar, we must ensure
      // their model value is considered.
      Trace("mbqi-model-enum") << "...converted " << queryCheck << std::endl;
      SubsolverSetupInfo ssi(d_env);
      Result r = checkWithSubsolver(queryCheck, ssi);
      if (r == Result::SAT)
      {
        // remember the updated query
        queryCurr = queryCheck;
        Trace("mbqi-model-enum") << "...success" << std::endl;
        Trace("mbqi-model-enum")
            << "* Enumerated " << q[0][ii] << " -> " << ret << std::endl;
        mvs[ii] = ret;
        vinst.add(q[0][ii], ret);
        success = true;
      }
      else if (!successEnum)
      {
        // we did not enumerate a candidate, and tried the original, which
        // failed.
        return false;
      }
    } while (!success);
  }
  return true;
}
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
