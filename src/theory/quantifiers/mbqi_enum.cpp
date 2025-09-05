/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Lydia Kondylidou, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for augmenting model-based instantiations via fast sygus enumeration.
 */

#include "theory/quantifiers/mbqi_enum.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "printer/smt2/smt2_printer.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/inst_strategy_mbqi.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "theory/smt_engine_subsolver.h"
#include "util/random.h"
#include "smt/set_defaults.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

void MVarInfo::initialize(Env& env,
                          const Node& q,
                          const Node& v,
                          const std::vector<Node>& etrules)
{
  NodeManager* nm = env.getNodeManager();
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
      Node vc = NodeManager::mkBoundVar(tnc);
      vs.push_back(vc);
    }
    d_lamVars = nm->mkNode(Kind::BOUND_VAR_LIST, vs);
    trules.insert(trules.end(), vs.begin(), vs.end());
  }
  // include free symbols from body of quantified formula if applicable
  if (env.getOptions().quantifiers.mbqiEnumFreeSymsGrammar)
  {
    std::unordered_set<Node> syms;
    expr::getSymbols(q[1], syms);
    trules.insert(trules.end(), syms.begin(), syms.end());
  }
  // include the external terminal rules
  for (const Node& symbol : etrules)
  {
    if (std::find(trules.begin(), trules.end(), symbol) == trules.end())
    {
      trules.push_back(symbol);
    }
  }
  Trace("mbqi-fast-enum") << "Symbols: " << trules << std::endl;
  SygusGrammarCons sgc;
  Node bvl;
  TypeNode tng = sgc.mkDefaultSygusType(env, retType, bvl, trules);
  if (TraceIsOn("mbqi-fast-enum"))
  {
    Trace("mbqi-fast-enum") << "Enumerate terms for " << retType;
    if (!d_lamVars.isNull())
    {
      Trace("mbqi-fast-enum") << ", variable list " << d_lamVars;
    }
    Trace("mbqi-fast-enum") << std::endl;
    Trace("mbqi-fast-enum") << "Based on grammar:" << std::endl;
    Trace("mbqi-fast-enum")
        << printer::smt2::Smt2Printer::sygusGrammarString(tng) << std::endl;
  }
  d_senum.reset(new SygusTermEnumerator(env, tng));
}

Node MVarInfo::getEnumeratedTerm(NodeManager* nm, size_t i)
{
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

void MQuantInfo::initialize(Env& env, InstStrategyMbqi& parent, const Node& q)
{
  // The externally provided terminal rules. This set is shared between
  // all variables we instantiate.
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
      // include variables defined in terms of others if applicable
      if (env.getOptions().quantifiers.mbqiEnumExtVarsGrammar)
      {
        etrules.push_back(v);
      }
    }
  }
  // include the global symbols if applicable
  if (env.getOptions().quantifiers.mbqiEnumGlobalSymGrammar)
  {
    const context::CDHashSet<Node>& gsyms = parent.getGlobalSyms();
    for (const Node& v : gsyms)
    {
      etrules.push_back(v);
    }
  }
  // initialize the variables we are instantiating
  for (size_t index : d_indices)
  {
    d_vinfo[index].initialize(env, q, q[0][index], etrules);
  }
}

MVarInfo& MQuantInfo::getVarInfo(size_t index)
{
  Assert(index < d_vinfo.size());
  return d_vinfo[index];
}

std::vector<size_t> MQuantInfo::getInstIndices() { return d_indices; }
std::vector<size_t> MQuantInfo::getNoInstIndices() { return d_nindices; }

bool MQuantInfo::shouldEnumerate(const TypeNode& tn)
{
  if (tn.isUninterpretedSort())
  {
    return false;
  }
  return true;
}

MbqiEnum::MbqiEnum(Env& env, InstStrategyMbqi& parent)
    : EnvObj(env), d_parent(parent)
{
  d_subOptions.copyValues(options());
  smt::SetDefaults::disableChecking(d_subOptions);
}

MQuantInfo& MbqiEnum::getOrMkQuantInfo(const Node& q)
{
  auto [it, inserted] = d_qinfo.try_emplace(q);
  if (inserted)
  {
    it->second.initialize(d_env, d_parent, q);
  }
  return it->second;
}

bool MbqiEnum::constructInstantiation(
    const Node& q,
    const Node& query,
    const std::vector<Node>& vars,
    std::vector<Node>& mvs,
    const std::map<Node, Node>& mvFreshVar,
    std::vector<std::pair<Node, InferenceId>>& auxLemmas)
{
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
  SubsolverSetupInfo ssi(d_env, d_subOptions);
  MQuantInfo& qi = getOrMkQuantInfo(q);
  std::vector<size_t> indices = qi.getInstIndices();
  std::vector<size_t> nindices = qi.getNoInstIndices();
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
  // consider variables in random order, for diversity of instantiations
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
      Node ret = vi.getEnumeratedTerm(nodeManager(), cindex);
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
  // try the instantiation
  return d_parent.tryInstantiation(
      q, mvs, InferenceId::QUANTIFIERS_INST_MBQI_ENUM, mvFreshVar);
}
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
