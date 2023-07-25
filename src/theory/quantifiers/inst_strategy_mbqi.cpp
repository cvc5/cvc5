/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
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

#include "theory/quantifiers/inst_strategy_mbqi.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "expr/subs.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/skolemize.h"
#include "theory/quantifiers/term_util.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/strings/theory_strings_utils.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

InstStrategyMbqi::InstStrategyMbqi(Env& env,
                                   QuantifiersState& qs,
                                   QuantifiersInferenceManager& qim,
                                   QuantifiersRegistry& qr,
                                   TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr)
{
  // some kinds may appear in model values that cannot be asserted
  d_nonClosedKinds.insert(STORE_ALL);
  d_nonClosedKinds.insert(CODATATYPE_BOUND_VARIABLE);
  d_nonClosedKinds.insert(UNINTERPRETED_SORT_VALUE);
}

void InstStrategyMbqi::reset_round(Theory::Effort e) { d_quantChecked.clear(); }

bool InstStrategyMbqi::needsCheck(Theory::Effort e)
{
  return e >= Theory::EFFORT_LAST_CALL;
}

QuantifiersModule::QEffort InstStrategyMbqi::needsModel(Theory::Effort e)
{
  return QEFFORT_MODEL;
}

void InstStrategyMbqi::check(Theory::Effort e, QEffort quant_e)
{
  if (e != Theory::EFFORT_LAST_CALL || quant_e != QEFFORT_MODEL)
  {
    return;
  }
  // see if the negation of each quantified formula is satisfiable in the model
  std::vector<Node> disj;
  FirstOrderModel* fm = d_treg.getModel();
  std::vector<TNode> visit;
  for (size_t i = 0, nquant = fm->getNumAssertedQuantifiers(); i < nquant; i++)
  {
    Node q = fm->getAssertedQuantifier(i);
    if (!d_qreg.hasOwnership(q, this))
    {
      continue;
    }
    process(q);
  }
}

bool InstStrategyMbqi::checkCompleteFor(Node q)
{
  return d_quantChecked.find(q) != d_quantChecked.end();
}

void InstStrategyMbqi::process(Node q)
{
  Assert(q.getKind() == FORALL);
  Trace("mbqi") << "Process quantified formula: " << q << std::endl;
  // Cache mapping terms in the skolemized body of q to the form passed to
  // the subsolver. This is local to this call.
  std::unordered_map<Node, Node> tmpConvertMap;
  // list of fresh variables per type
  std::map<TypeNode, std::unordered_set<Node> > freshVarType;
  // model values to the fresh variables
  std::map<Node, Node> mvToFreshVar;

  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  const RepSet* rs = d_treg.getModel()->getRepSet();
  FirstOrderModel* fm = d_treg.getModel();

  // allocate the skolem variables
  Subs skolems;
  for (const Node& v : q[0])
  {
    Node k = sm->mkPurifySkolem(v);
    skolems.add(v, k);
    // do not take its model value (which does not exist) in conversion below
    tmpConvertMap[k] = k;
  }
  // compute the skolemization in a separate traversal instead of mapping
  // bound variables to skolems. This is to ensure we avoid variable shadowing
  // for model values for functions
  Node skq = skolems.apply(q[1]);
  // convert to query
  Node cbody = convertToQuery(skq, tmpConvertMap, freshVarType);
  Trace("mbqi") << "- converted body: " << cbody << std::endl;

  // check if there are any bad kinds
  if (cbody.isNull())
  {
    Trace("mbqi") << "...failed to convert to query" << std::endl;
    return;
  }
  Assert(!expr::hasSubtermKinds(d_nonClosedKinds, cbody));

  std::vector<Node> constraints;

  // constraint: the negation of the skolemized body
  Node bquery = rewrite(cbody.negate());
  if (!bquery.isConst())
  {
    constraints.push_back(bquery);
  }
  else if (!bquery.getConst<bool>())
  {
    d_quantChecked.insert(q);
    Trace("mbqi") << "...success, by rewriting" << std::endl;
    return;
  }
  // ensure the entire domain of uninterpreted sorts are converted
  std::unordered_set<TypeNode> processedUsort;
  for (const Node& k : skolems.d_subs)
  {
    TypeNode tn = k.getType();
    if (!tn.isUninterpretedSort()
        || processedUsort.find(tn) != processedUsort.end())
    {
      continue;
    }
    processedUsort.insert(tn);
    const std::vector<Node>* treps = rs->getTypeRepsOrNull(tn);
    if (treps != nullptr)
    {
      for (const Node& r : *treps)
      {
        Node rv = fm->getValue(r);
        Assert(rv.getKind() == kind::UNINTERPRETED_SORT_VALUE);
        convertToQuery(rv, tmpConvertMap, freshVarType);
      }
    }
  }
  // constraint: the skolems of the given type are equal to one of the variables
  // introduced for uninterpreted sorts
  std::map<TypeNode, std::unordered_set<Node> >::iterator itk;
  for (const Node& k : skolems.d_subs)
  {
    TypeNode tn = k.getType();
    itk = freshVarType.find(tn);
    if (itk == freshVarType.end())
    {
      // not an uninterpreted sort, continue
      continue;
    }
    if (itk->second.empty())
    {
      Trace("mbqi") << "warning: failed to get vars for type " << tn
                    << std::endl;
      // this should never happen but we explicitly guard for it, since
      // otherwise we would be model unsound below
      Assert(false);
      continue;
    }
    std::vector<Node> disj;
    for (const Node& fv : itk->second)
    {
      disj.push_back(k.eqNode(fv));
    }
    Node instCardCons = nm->mkOr(disj);
    constraints.push_back(instCardCons);
  }

  // constraint: distinctness of variables introduced for uninterpreted
  // constants
  std::vector<Node> allVars;
  for (const std::pair<const TypeNode, std::unordered_set<Node> >& fv :
       freshVarType)
  {
    Assert(!fv.second.empty());
    allVars.insert(allVars.end(), fv.second.begin(), fv.second.end());
    if (fv.second.size() > 1)
    {
      std::vector<Node> fvars(fv.second.begin(), fv.second.end());
      constraints.push_back(nm->mkNode(DISTINCT, fvars));
    }
  }

  // make the query
  Node query = nm->mkAnd(constraints);

  std::unique_ptr<SolverEngine> mbqiChecker;
  initializeSubsolver(mbqiChecker, d_env);
  mbqiChecker->setOption("produce-models", "true");
  mbqiChecker->assertFormula(query);
  Trace("mbqi") << "*** Check sat..." << std::endl;
  Trace("mbqi") << "  query is : " << query << std::endl;
  Result r = mbqiChecker->checkSat();
  Trace("mbqi") << "  ...got : " << r << std::endl;
  if (r.getStatus() == Result::UNSAT)
  {
    d_quantChecked.insert(q);
    Trace("mbqi") << "...success, SAT" << std::endl;
    return;
  }

  // get the model values for all fresh variables
  for (const Node& v : allVars)
  {
    Node mv = mbqiChecker->getValue(v);
    Assert(mvToFreshVar.find(mv) == mvToFreshVar.end());
    mvToFreshVar[mv] = v;
    Trace("mbqi-debug") << "mvToFreshVar " << mv << " is " << v << std::endl;
  }

  // get the model values for skolems
  std::vector<Node> terms;
  getModelFromSubsolver(*mbqiChecker.get(), skolems.d_subs, terms);
  Assert(skolems.size() == terms.size());
  if (TraceIsOn("mbqi"))
  {
    Trace("mbqi") << "...model from subsolver is: " << std::endl;
    for (size_t i = 0, nterms = skolems.size(); i < nterms; i++)
    {
      Trace("mbqi") << "  " << skolems.d_subs[i] << " -> " << terms[i]
                    << std::endl;
    }
  }
  // try to convert those terms to an instantiation
  tmpConvertMap.clear();
  for (Node& v : terms)
  {
    Node vc = convertFromModel(v, tmpConvertMap, mvToFreshVar);
    if (vc.isNull())
    {
      Trace("mbqi") << "...failed to convert " << v << " from model" << std::endl;
      return;
    }
    if (expr::hasSubtermKinds(d_nonClosedKinds, vc))
    {
      Trace("mbqi") << "warning: failed to process model value " << vc
                    << ", from " << v
                    << ", use arbitrary term for instantiation" << std::endl;
      vc = nm->mkGroundTerm(v.getType());
    }
    v = vc;
  }

  // get a term that has the same model value as the value each fresh variable
  // represents
  Subs fvToInst;
  for (const Node& v : allVars)
  {
    // get a term that witnesses this variable
    Node ov = sm->getOriginalForm(v);
    Node mvt = rs->getTermForRepresentative(ov);
    // ensure that this term does not contain cex variables, in case CEQGI
    // is combined with MBQI
    if (mvt.isNull() || !TermUtil::getInstConstAttr(mvt).isNull())
    {
      Trace("mbqi") << "warning: failed to get term from value " << ov
                    << ", use arbitrary term in query" << std::endl;
      mvt = nm->mkGroundTerm(ov.getType());
    }
    Assert(v.getType() == mvt.getType());
    fvToInst.add(v, mvt);
  }

  // now convert fresh variables into terms
  for (Node& v : terms)
  {
    v = fvToInst.apply(v);
  }

  // try to add instantiation
  Instantiate* qinst = d_qim.getInstantiate();
  if (!qinst->addInstantiation(q, terms, InferenceId::QUANTIFIERS_INST_MBQI))
  {
    Trace("mbqi") << "...failed to add instantiation" << std::endl;
    return;
  }
  Trace("mbqi") << "...success, instantiated" << std::endl;
}

Node InstStrategyMbqi::convertToQuery(
    Node t,
    std::unordered_map<Node, Node>& cmap,
    std::map<TypeNode, std::unordered_set<Node> >& freshVarType)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  FirstOrderModel* fm = d_treg.getModel();
  std::unordered_map<Node, Node>::iterator it;
  std::map<Node, Node> modelValue;
  std::unordered_set<Node> processingChildren;
  std::vector<TNode> visit;
  visit.push_back(t);
  TNode cur;
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = cmap.find(cur);
    Trace("mbqi-debug") << "convertToQuery: " << cur << " " << cur.getKind()
                        << " " << cur.getType() << std::endl;
    if (it != cmap.end())
    {
      // already computed
      continue;
    }
    if (processingChildren.find(cur) == processingChildren.end())
    {
      Kind ck = cur.getKind();
      if (ck == BOUND_VARIABLE)
      {
        cmap[cur] = cur;
      }
      else if (ck == UNINTERPRETED_SORT_VALUE)
      {
        // return the fresh variable for this term
        Node k = sm->mkPurifySkolem(cur);
        freshVarType[cur.getType()].insert(k);
        cmap[cur] = k;
        continue;
      }
      else if (ck == CONST_SEQUENCE || cur.isVar())
      {
        // constant sequences and variables require two passes
        if (!cur.getType().isFirstClass())
        {
          // can be e.g. tester/constructor/selector
          cmap[cur] = cur;
        }
        else
        {
          std::map<Node, Node>::iterator itm = modelValue.find(cur);
          if (itm == modelValue.end())
          {
            Node mval;
            if (ck == CONST_SEQUENCE)
            {
              mval = strings::utils::mkConcatForConstSequence(cur);
            }
            else
            {
              mval = fm->getValue(cur);
            }
            Trace("mbqi-model") << "  M[" << cur << "] = " << mval << "\n";
            modelValue[cur] = mval;
            if (cur == mval)
            {
              // failed to evaluate in model, keep itself
              cmap[cur] = cur;
            }
            else
            {
              visit.push_back(cur);
              visit.push_back(mval);
            }
          }
          else
          {
            Assert(cmap.find(itm->second) != cmap.end())
                << "Missing " << itm->second;
            cmap[cur] = cmap[itm->second];
          }
        }
      }
      else if (cur.getNumChildren() == 0)
      {
        // if this is a bad kind, fail immediately
        if (d_nonClosedKinds.find(ck) != d_nonClosedKinds.end())
        {
          return Node::null();
        }
        cmap[cur] = cur;
      }
      else
      {
        processingChildren.insert(cur);
        visit.push_back(cur);
        if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
        {
          visit.push_back(cur.getOperator());
        }
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      continue;
    }
    processingChildren.erase(cur);
    bool childChanged = false;
    std::vector<Node> children;
    if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      children.push_back(cur.getOperator());
    }
    children.insert(children.end(), cur.begin(), cur.end());
    for (Node& cn : children)
    {
      it = cmap.find(cn);
      Assert(it != cmap.end());
      Assert(!it->second.isNull());
      childChanged = childChanged || cn != it->second;
      cn = it->second;
    }
    Node ret = cur;
    if (childChanged)
    {
      ret = rewrite(nm->mkNode(cur.getKind(), children));
    }
    cmap[cur] = ret;
  } while (!visit.empty());

  Assert(cmap.find(cur) != cmap.end());
  return cmap[cur];
}

Node InstStrategyMbqi::convertFromModel(
    Node t,
    std::unordered_map<Node, Node>& cmap,
    const std::map<Node, Node>& mvToFreshVar)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<Node, Node>::iterator it;
  std::map<Node, Node> modelValue;
  std::unordered_set<Node> processingChildren;
  std::vector<TNode> visit;
  visit.push_back(t);
  TNode cur;
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = cmap.find(cur);
    Trace("mbqi-debug") << "convertFromModel: " << cur << " " << cur.getKind()
                        << " " << cur.getType() << std::endl;
    if (it != cmap.end())
    {
      // already computed
      continue;
    }
    if (processingChildren.find(cur) == processingChildren.end())
    {
      Kind ck = cur.getKind();
      if (ck == UNINTERPRETED_SORT_VALUE)
      {
        // converting from query, find the variable that it is equal to
        std::map<Node, Node>::const_iterator itmv = mvToFreshVar.find(cur);
        if (itmv != mvToFreshVar.end())
        {
          cmap[cur] = itmv->second;
        }
        else
        {
          // TODO (wishue #143): could convert RAN to witness term here
          // failed to find equal, we fail
          return Node::null();
        }
      }
      else if (ck == CONST_SEQUENCE)
      {
        // must convert to concat of sequence units
        Node cconv = strings::utils::mkConcatForConstSequence(cur);
        cmap[cur] = convertFromModel(cconv, cmap, mvToFreshVar);
      }
      else if (cur.getNumChildren() == 0)
      {
        cmap[cur] = cur;
      }
      else
      {
        processingChildren.insert(cur);
        visit.push_back(cur);
        if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
        {
          visit.push_back(cur.getOperator());
        }
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      continue;
    }
    processingChildren.erase(cur);
    bool childChanged = false;
    std::vector<Node> children;
    if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      children.push_back(cur.getOperator());
    }
    children.insert(children.end(), cur.begin(), cur.end());
    for (Node& cn : children)
    {
      it = cmap.find(cn);
      Assert(it != cmap.end());
      Assert(!it->second.isNull());
      childChanged = childChanged || cn != it->second;
      cn = it->second;
    }
    Node ret = cur;
    if (childChanged)
    {
      ret = rewrite(nm->mkNode(cur.getKind(), children));
    }
    cmap[cur] = ret;
  } while (!visit.empty());

  Assert(cmap.find(cur) != cmap.end());
  return cmap[cur];
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
