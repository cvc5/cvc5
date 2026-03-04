/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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
#include "expr/subs.h"
#include "printer/smt2/smt2_printer.h"
#include "smt/set_defaults.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/inst_strategy_mbqi.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "theory/smt_engine_subsolver.h"
#include "util/random.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class MbqiEnumTermEnumeratorCallback : protected EnvObj,
                                       public SygusTermEnumeratorCallback
{
 public:
  MbqiEnumTermEnumeratorCallback(Env& env) : EnvObj(env) {}
  virtual ~MbqiEnumTermEnumeratorCallback() {}
  /** Filter duplicate/invalid built-in terms during SyGuS enumeration. */
  bool addTerm(const Node& n, std::unordered_set<Node>& bterms) override
  {
    Node bn = datatypes::utils::sygusToBuiltin(n);
    bn = extendedRewrite(bn);
    if (bterms.find(bn) != bterms.end())
    {
      return false;
    }
    if (bn.getKind() == Kind::WITNESS)
    {
      if (!expr::hasSubterm(bn[1], bn[0][0]))
      {
        return false;
      }
    }
    bterms.insert(bn);
    return true;
  }
};

bool introduceChoice(const Options& opts,
                     const TypeNode& tn,
                     const TypeNode& retType)
{
  // never for Booleans or functions
  if (tn.isBoolean() || tn.isFunction())
  {
    return false;
  }
  if (opts.quantifiers.mbqiEnumChoiceGrammarAll)
  {
    return true;
  }
  return tn == retType;
}

bool shouldEnumerate(const Options& opts, const TypeNode& tn)
{
  // It may make sense to enumerate choice for FO uninterpreted sorts, but
  // seems to not work well in practice.
  if (tn.isUninterpretedSort())
  {
    return false;
  }
  return true;
}

void MVarInfo::initialize(Env& env,
                          const Node& q,
                          const Node& v,
                          const std::vector<Node>& etrules)
{
  NodeManager* nm = env.getNodeManager();
  TypeNode tn = v.getType();
  Assert(shouldEnumerate(env.getOptions(), tn));
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
  Trace("mbqi-enum-grammar") << "Symbols: " << trules << std::endl;
  SygusGrammarCons sgc;
  Node bvl;
  TypeNode tng = sgc.mkDefaultSygusType(env, retType, bvl, trules);
  if (TraceIsOn("mbqi-enum"))
  {
    Trace("mbqi-enum") << "Enumerate terms for " << retType;
    if (!d_lamVars.isNull())
    {
      Trace("mbqi-enum") << ", variable list " << d_lamVars;
    }
    Trace("mbqi-enum") << std::endl;
    Trace("mbqi-enum-grammar") << "Based on grammar:" << std::endl;
    Trace("mbqi-enum-grammar")
        << printer::smt2::Smt2Printer::sygusGrammarString(tng) << std::endl;
  }
  TypeNode tuse = tng;
  const Options& opts = env.getOptions();
  if (opts.quantifiers.mbqiEnumChoiceGrammar)
  {
    // we will be eliminating choice
    d_cenc.reset(new ChoiceElimNodeConverter(nm));
    TypeNode bt = nm->booleanType();
    // take the original grammar
    SygusGrammar sgg({}, tng);
    const std::vector<Node>& nts = sgg.getNtSyms();
    std::vector<Node> ntAll = nts;
    // Note we have to delay adding rules to the final combined grammar until
    // all the non-terminals have been determined. This means we have to
    // remember temporary information here. Note this would be easier if we
    // could add non-terminals to grammars dynamically.
    std::map<TypeNode, std::shared_ptr<SygusGrammar>> typeToPredGrammar;
    std::map<TypeNode, Node> typeToWitnessRule;
    for (const Node& nt : nts)
    {
      TypeNode ntt = nt.getType();
      // choice for Boolean is not worthwhile
      // in the rare case multiple nonterminals of the same type, skip
      if (!introduceChoice(opts, ntt, retType)
          || typeToPredGrammar.find(ntt) != typeToPredGrammar.end())
      {
        continue;
      }
      // not Boolean?
      Node x = nm->mkBoundVar("x", ntt);
      trules.push_back(x);
      Trace("mbqi-enum-choice-grammar")
          << "Make predicate grammar " << trules << std::endl;
      TypeNode tnb = sgc.mkDefaultSygusType(env, bt, bvl, trules);
      Trace("mbqi-enum-choice-grammar") << "Predicate grammar:" << std::endl;
      Trace("mbqi-enum-choice-grammar")
          << printer::smt2::Smt2Printer::sygusGrammarString(tnb) << std::endl;
      std::vector<Node> emptyVec;
      typeToPredGrammar[ntt] = std::make_shared<SygusGrammar>(emptyVec, tnb);
      SygusGrammar& sgb = *typeToPredGrammar[ntt].get();
      const std::vector<Node>& ntsb = sgb.getNtSyms();
      ntAll.insert(ntAll.end(), ntsb.begin(), ntsb.end());
      Node ntBool;
      for (const Node& snt : ntsb)
      {
        if (snt.getType().isBoolean())
        {
          Trace("mbqi-enum-choice-grammar")
              << "...found " << ntBool << std::endl;
          ntBool = snt;
          break;
        }
      }
      Assert(!ntBool.isNull());
      Node witness = nm->mkNode(
          Kind::WITNESS, nm->mkNode(Kind::BOUND_VAR_LIST, x), ntBool);
      typeToWitnessRule[ntt] = witness;
      trules.pop_back();
    }
    if (!typeToPredGrammar.empty())
    {
      Trace("mbqi-enum-choice-grammar")
          << "Make combined " << ntAll << std::endl;
      SygusGrammar sgcom({}, ntAll);
      // get the non-terminal for Bool of the predicate grammar
      Trace("mbqi-enum-choice-grammar")
          << "Find non-terminal Bool in predicate grammar..." << std::endl;
      // fill in the predicate grammars
      for (std::pair<const TypeNode, std::shared_ptr<SygusGrammar>>& tpg :
           typeToPredGrammar)
      {
        SygusGrammar& sgb = *tpg.second.get();
        const std::vector<Node>& ntsb = sgb.getNtSyms();
        for (const Node& nt : ntsb)
        {
          const std::vector<Node>& rules = sgb.getRulesFor(nt);
          sgcom.addRules(nt, rules);
        }
      }
      // fill in the main grammar
      for (const Node& nt : nts)
      {
        Trace("mbqi-enum-choice-grammar")
            << "- non-terminal in sgg: " << nt << std::endl;
        std::vector<Node> rules = sgg.getRulesFor(nt);
        TypeNode ntt = nt.getType();
        if (introduceChoice(opts, ntt, retType))
        {
          Assert(typeToWitnessRule.find(ntt) != typeToWitnessRule.end());
          Node witness = typeToWitnessRule[ntt];
          Trace("mbqi-enum-choice-grammar")
              << "...add " << witness << " to " << nt << std::endl;
          rules.insert(rules.begin(), witness);
        }
        sgcom.addRules(nt, rules);
      }
      TypeNode gcom = sgcom.resolve();
      Trace("mbqi-enum-choice-grammar") << "Combined grammar:" << std::endl;
      Trace("mbqi-enum-choice-grammar")
          << printer::smt2::Smt2Printer::sygusGrammarString(gcom) << std::endl;
      tuse = gcom;
      d_senumCb.reset(new MbqiEnumTermEnumeratorCallback(env));
    }
  }
  d_senum.reset(new SygusTermEnumerator(env, tuse, d_senumCb.get()));
}

MVarInfo::ChoiceElimNodeConverter::ChoiceElimNodeConverter(NodeManager* nm)
    : NodeConverter(nm)
{
}
Node MVarInfo::ChoiceElimNodeConverter::postConvert(Node n)
{
  if (n.getKind() == Kind::WITNESS)
  {
    NodeManager* nm = d_nm;
    Trace("mbqi-enum-choice-grammar") << "---> convert " << n << std::endl;
    std::unordered_set<Node> fvs;
    expr::getFreeVariables(n, fvs);
    Node exists = nm->mkNode(Kind::FORALL, n[0], n[1].negate());
    TypeNode retType = n[0][0].getType();
    std::vector<TypeNode> argTypes;
    std::vector<Node> ubvl;
    for (const Node& v : fvs)
    {
      ubvl.push_back(v);
      argTypes.push_back(v.getType());
    }
    if (!argTypes.empty())
    {
      retType = nm->mkFunctionType(argTypes, retType);
    }
    SkolemManager* skm = nm->getSkolemManager();
    Node sym = skm->mkInternalSkolemFunction(
        InternalSkolemId::MBQI_CHOICE_FUN, retType, {n});
    Trace("mbqi-enum-choice-fun")
        << "Choice: " << sym << " for " << n << std::endl;
    Node h = sym;
    if (!ubvl.empty())
    {
      std::vector<Node> wchildren;
      wchildren.push_back(h);
      wchildren.insert(wchildren.end(), ubvl.begin(), ubvl.end());
      h = nm->mkNode(Kind::APPLY_UF, wchildren);
    }
    Assert(h.getType() == n.getType());
    Subs subs;
    subs.add(n[0][0], h);
    Node kpred = subs.apply(n[1]);
    Node lem = nm->mkNode(Kind::OR, exists, kpred);
    if (!ubvl.empty())
    {
      // use h(x) as the trigger, which is a legal trigger since it is applied
      // to the exact variable list of the quantified formula.
      Node ipl = nm->mkNode(Kind::INST_PATTERN_LIST,
                            nm->mkNode(Kind::INST_PATTERN, h));
      lem = nm->mkNode(
          Kind::FORALL, nm->mkNode(Kind::BOUND_VAR_LIST, ubvl), lem, ipl);
    }
    Trace("mbqi-enum-debug") << "TMP " << sym << " for " << n << std::endl;
    Trace("mbqi-enum-choice-grammar") << "-----> lemma " << lem << std::endl;
    d_lemmas[sym] = lem;
    return h;
  }
  return n;
}

std::vector<std::pair<Node, InferenceId>> MVarInfo::getEnumeratedLemmas(
    const Node& t)
{
  std::vector<std::pair<Node, InferenceId>> lemmas;
  if (d_cenc != nullptr)
  {
    lemmas = d_cenc->getEnumeratedLemmas(t);
  }
  return lemmas;
}

std::vector<std::pair<Node, InferenceId>>
MVarInfo::ChoiceElimNodeConverter::getEnumeratedLemmas(const Node& t)
{
  std::vector<std::pair<Node, InferenceId>> lemmas;
  std::unordered_set<Node> syms;
  expr::getSymbols(t, syms, d_visited);
  Trace("mbqi-enum-debug") << "getEnumeratedLemmas for " << t << std::endl;
  std::map<Node, Node>::iterator itl;
  for (const Node& s : syms)
  {
    Trace("mbqi-enum-debug") << "...is lemma sym " << s << "?" << std::endl;
    itl = d_lemmas.find(s);
    if (itl != d_lemmas.end())
    {
      lemmas.emplace_back(itl->second,
                          InferenceId::QUANTIFIERS_MBQI_ENUM_CHOICE);
    }
  }
  return lemmas;
}

Node MVarInfo::getEnumeratedTerm(NodeManager* nm, size_t i)
{
  size_t nullCount = 0;
  while (i >= d_enum.size())
  {
    Node curr = d_senum->getCurrent();
    Trace("mbqi-enum-debug") << "Enumerate: " << curr << std::endl;
    if (!curr.isNull())
    {
      // use converter if it exists
      if (d_cenc != nullptr)
      {
        curr = d_cenc->convert(curr);
      }
      if (!d_lamVars.isNull())
      {
        curr = nm->mkNode(Kind::LAMBDA, d_lamVars, curr);
      }
      Assert(!curr.isNull());
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
    Trace("mbqi-enum-debug") << "... return null" << std::endl;
    return Node::null();
  }
  Assert(!d_enum[i].isNull());
  return d_enum[i];
}

void MQuantInfo::initialize(Env& env, InstStrategyMbqi& parent, const Node& q)
{
  // The externally provided terminal rules. This set is shared between
  // all variables we instantiate.
  std::vector<Node> etrules;
  // include the global symbols if applicable
  if (env.getOptions().quantifiers.mbqiEnumGlobalSymGrammar)
  {
    const context::CDHashSet<Node>& gsyms = parent.getGlobalSyms();
    for (const Node& v : gsyms)
    {
      etrules.push_back(v);
    }
  }
  for (const Node& v : q[0])
  {
    size_t index = d_vinfo.size();
    d_vinfo.emplace_back();
    TypeNode vtn = v.getType();
    // if enumerated, add to list
    if (shouldEnumerate(env.getOptions(), vtn))
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
  // initialize the variables we are instantiating
  for (size_t index : d_indices)
  {
    // initialize the variables we are instantiating
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

MbqiEnum::MbqiEnum(Env& env, InstStrategyMbqi& parent)
    : EnvObj(env), d_parent(parent)
{
  d_subOptions.copyValues(options());
  d_subOptions.write_quantifiers().instMaxRounds = 5;
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
  if (TraceIsOn("mbqi-enum"))
  {
    Trace("mbqi-enum") << "Instantiate " << q << std::endl;
    for (size_t i = 0, nvars = vars.size(); i < nvars; i++)
    {
      Trace("mbqi-enum") << "  " << q[0][i] << " -> " << mvs[i] << std::endl;
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
      Trace("mbqi-enum-model") << "Failed to convert " << v << std::endl;
      return false;
    }
    Trace("mbqi-enum-model")
        << "* Assume: " << q[0][i] << " -> " << v << std::endl;
    // if we don't enumerate it, we are already considering this instantiation
    inst.add(vars[i], v);
    vinst.add(q[0][i], v);
  }
  Node queryCurr = query;
  Trace("mbqi-enum-model") << "...query is " << queryCurr << std::endl;
  queryCurr = rewrite(inst.apply(queryCurr));
  Trace("mbqi-enum-model") << "...processed is " << queryCurr << std::endl;
  // consider variables in random order, for diversity of instantiations
  std::shuffle(indices.begin(), indices.end(), Random::getRandom());
  bool addedInst = false;
  for (size_t i = 0, isize = indices.size(); i < isize; i++)
  {
    size_t ii = indices[i];
    TNode v = vars[ii];
    MVarInfo& vi = qi.getVarInfo(ii);
    size_t cindex = 0;
    bool success = false;
    bool successEnum;
    bool lastVar = (i + 1 == isize);
    do
    {
      Node ret = vi.getEnumeratedTerm(nodeManager(), cindex);
      cindex++;
      Node retc;
      if (!ret.isNull())
      {
        Trace("mbqi-enum-debug")
            << "TMP - Try candidate: " << q.getId() << " " << v << " " << cindex
            << " " << ret << std::endl;
        Trace("mbqi-enum") << "- Try candidate: " << ret << std::endl;
        // apply current substitution (to account for cases where ret has
        // other variables in its grammar).
        ret = vinst.apply(ret);
        retc = ret;
        successEnum = true;
        // now convert the value
        std::unordered_map<Node, Node> tmpConvertMap;
        std::map<TypeNode, std::unordered_set<Node>> freshVarType;
        retc = d_parent.convertToQuery(retc, tmpConvertMap, freshVarType);
      }
      else
      {
        Trace("mbqi-enum-debug")
            << "- Failed to enumerate candidate" << std::endl;
        // if we failed to enumerate, just try the original
        Node mc = d_parent.convertFromModel(mvs[ii], tmpCMap, mvFreshVar);
        if (mc.isNull())
        {
          Trace("mbqi-enum-debug")
              << "Failed to convert " << mvs[ii] << std::endl;
          // if failed to convert, we fail
          return false;
        }
        ret = mc;
        retc = mc;
        successEnum = false;
      }
      Trace("mbqi-enum-model")
          << "- Converted candidate: " << v << " -> " << retc << std::endl;
      Node queryCheck;
      // see if it is still satisfiable, if still SAT, we replace
      queryCheck = queryCurr.substitute(v, TNode(retc));
      queryCheck = rewrite(queryCheck);
      Trace("mbqi-enum-model") << "...check " << queryCheck << std::endl;
      Result r = d_parent.checkWithSubsolverSimple(queryCheck, ssi);
      success = (r != Result::UNSAT);
      if (success)
      {
        // remember the updated query
        queryCurr = queryCheck;
        Trace("mbqi-enum-model") << "...success" << std::endl;
        Trace("mbqi-enum") << "* Enumerated " << q[0][ii] << " -> " << ret
                           << std::endl;
        mvs[ii] = ret;
        vinst.add(q[0][ii], ret);
      }
      // We verify the lemma is successfully added here. If it is not, then
      // success is false and we continue the enumeration.
      if (lastVar && success)
      {
        success = d_parent.tryInstantiation(
            q, mvs, InferenceId::QUANTIFIERS_INST_MBQI_ENUM, mvFreshVar);
        addedInst = addedInst || success;
      }

      if (!success && !successEnum)
      {
        // we did not enumerate a candidate, and tried the original, which
        // failed.
        Trace("mbqi-enum-debug") << "Failed to enumerate" << std::endl;
        return false;
      }
    } while (!success);
  }
  // See if there are auxiliary lemmas, if so, add them to the returned
  // vector.
  Trace("mbqi-enum-debug") << "Instantiate: " << q.getId() << std::endl;
  for (size_t i = 0, isize = indices.size(); i < isize; i++)
  {
    size_t ii = indices[i];
    TNode v = vars[ii];
    Trace("mbqi-enum-debug") << "- " << v << " -> " << mvs[ii] << std::endl;
    MVarInfo& vi = qi.getVarInfo(ii);
    std::vector<std::pair<Node, InferenceId>> alv =
        vi.getEnumeratedLemmas(mvs[ii]);
    Trace("mbqi-enum-debug")
        << "..." << alv.size() << " aux lemmas" << std::endl;
    auxLemmas.insert(auxLemmas.end(), alv.begin(), alv.end());
  }
  return addedInst;
}
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
