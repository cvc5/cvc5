/*********************                                                        */
/*! \file expand_definitions.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of expand definitions for an SMT engine.
 **/

#include "smt/expand_definitions.h"

#include <stack>
#include <utility>

#include "expr/node_manager_attributes.h"
#include "smt/defined_function.h"
#include "smt/smt_engine.h"
#include "theory/theory_engine.h"

using namespace CVC4::preprocessing;
using namespace CVC4::theory;
using namespace CVC4::kind;

namespace CVC4 {
namespace smt {

ExpandDefs::ExpandDefs(SmtEngine& smt,
                       ResourceManager& rm,
                       SmtEngineStatistics& stats)
    : d_smt(smt), d_resourceManager(rm), d_smtStats(stats), d_tpg(nullptr)
{
}

ExpandDefs::~ExpandDefs() {}

Node ExpandDefs::expandDefinitions(
    TNode n,
    std::unordered_map<Node, Node, NodeHashFunction>& cache,
    bool expandOnly)
{
  TrustNode trn = expandDefinitions(n, cache, expandOnly, nullptr);
  return trn.isNull() ? Node(n) : trn.getNode();
}

TrustNode ExpandDefs::expandDefinitions(
    TNode n,
    std::unordered_map<Node, Node, NodeHashFunction>& cache,
    bool expandOnly,
    TConvProofGenerator* tpg)
{
  const TNode orig = n;
  NodeManager* nm = d_smt.getNodeManager();
  std::stack<std::tuple<Node, Node, bool>> worklist;
  std::stack<Node> result;
  worklist.push(std::make_tuple(Node(n), Node(n), false));
  // The worklist is made of triples, each is input / original node then the
  // output / rewritten node and finally a flag tracking whether the children
  // have been explored (i.e. if this is a downward or upward pass).

  do
  {
    d_resourceManager.spendResource(ResourceManager::Resource::PreprocessStep);

    // n is the input / original
    // node is the output / result
    Node node;
    bool childrenPushed;
    std::tie(n, node, childrenPushed) = worklist.top();
    worklist.pop();

    // Working downwards
    if (!childrenPushed)
    {
      Kind k = n.getKind();

      // we can short circuit (variable) leaves
      if (n.isVar())
      {
        SmtEngine::DefinedFunctionMap* dfuns = d_smt.getDefinedFunctionMap();
        SmtEngine::DefinedFunctionMap::const_iterator i = dfuns->find(n);
        if (i != dfuns->end())
        {
          Node f = (*i).second.getFormula();
          const std::vector<Node>& formals = (*i).second.getFormals();
          // replacement must be closed
          if (!formals.empty())
          {
            f = nm->mkNode(LAMBDA, nm->mkNode(BOUND_VAR_LIST, formals), f);
          }
          // are we are producing proofs for this call?
          if (tpg != nullptr)
          {
            // if this is a variable, we can simply assume it
            // ------- ASSUME
            // n = f
            Node conc = n.eqNode(f);
            tpg->addRewriteStep(n, f, PfRule::ASSUME, {}, {conc}, true);
          }
          // must recursively expand its definition
          TrustNode tfe = expandDefinitions(f, cache, expandOnly, tpg);
          Node fe = tfe.isNull() ? f : tfe.getNode();
          // don't bother putting in the cache
          result.push(fe);
          continue;
        }
        // don't bother putting in the cache
        result.push(n);
        continue;
      }

      // maybe it's in the cache
      std::unordered_map<Node, Node, NodeHashFunction>::iterator cacheHit =
          cache.find(n);
      if (cacheHit != cache.end())
      {
        TNode ret = (*cacheHit).second;
        result.push(ret.isNull() ? n : ret);
        continue;
      }

      // otherwise expand it
      bool doExpand = false;
      if (k == APPLY_UF)
      {
        // Always do beta-reduction here. The reason is that there may be
        // operators such as INTS_MODULUS in the body of the lambda that would
        // otherwise be introduced by beta-reduction via the rewriter, but are
        // not expanded here since the traversal in this function does not
        // traverse the operators of nodes. Hence, we beta-reduce here to
        // ensure terms in the body of the lambda are expanded during this
        // call.
        if (n.getOperator().getKind() == LAMBDA)
        {
          doExpand = true;
        }
        else
        {
          // We always check if this operator corresponds to a defined function.
          doExpand = d_smt.isDefinedFunction(n.getOperator().toExpr());
        }
      }
      // the premise of the proof of expansion (if we are expanding a definition
      // and proofs are enabled)
      std::vector<Node> pfExpChildren;
      if (doExpand)
      {
        std::vector<Node> formals;
        TNode fm;
        if (n.getOperator().getKind() == LAMBDA)
        {
          TNode op = n.getOperator();
          // lambda
          for (unsigned i = 0; i < op[0].getNumChildren(); i++)
          {
            formals.push_back(op[0][i]);
          }
          fm = op[1];
        }
        else
        {
          // application of a user-defined symbol
          TNode func = n.getOperator();
          SmtEngine::DefinedFunctionMap* dfuns = d_smt.getDefinedFunctionMap();
          SmtEngine::DefinedFunctionMap::const_iterator i = dfuns->find(func);
          if (i == dfuns->end())
          {
            throw TypeCheckingException(
                n.toExpr(),
                std::string("Undefined function: `") + func.toString() + "'");
          }
          DefinedFunction def = (*i).second;
          formals = def.getFormals();

          if (Debug.isOn("expand"))
          {
            Debug("expand") << "found: " << n << std::endl;
            Debug("expand") << " func: " << func << std::endl;
            std::string name = func.getAttribute(expr::VarNameAttr());
            Debug("expand") << "     : \"" << name << "\"" << std::endl;
          }
          if (Debug.isOn("expand"))
          {
            Debug("expand") << " defn: " << def.getFunction() << std::endl
                            << "       [";
            if (formals.size() > 0)
            {
              copy(formals.begin(),
                   formals.end() - 1,
                   std::ostream_iterator<Node>(Debug("expand"), ", "));
              Debug("expand") << formals.back();
            }
            Debug("expand")
                << "]" << std::endl
                << "       " << def.getFunction().getType() << std::endl
                << "       " << def.getFormula() << std::endl;
          }

          fm = def.getFormula();
          // are we producing proofs for this call?
          if (tpg != nullptr)
          {
            Node pfRhs = fm;
            if (!formals.empty())
            {
              Node bvl = nm->mkNode(BOUND_VAR_LIST, formals);
              pfRhs = nm->mkNode(LAMBDA, bvl, pfRhs);
            }
            Assert(func.getType().isComparableTo(pfRhs.getType()));
            pfExpChildren.push_back(func.eqNode(pfRhs));
          }
        }

        Node instance = fm.substitute(formals.begin(),
                                      formals.end(),
                                      n.begin(),
                                      n.begin() + formals.size());
        Debug("expand") << "made : " << instance << std::endl;
        // are we producing proofs for this call?
        if (tpg != nullptr)
        {
          if (n != instance)
          {
            // This code is run both when we are doing expand definitions and
            // simple beta reduction.
            //
            // f = (lambda ((x T)) t)  [if we are expanding a definition]
            // ---------------------- MACRO_SR_PRED_INTRO
            // n = instance
            Node conc = n.eqNode(instance);
            tpg->addRewriteStep(n,
                                instance,
                                PfRule::MACRO_SR_PRED_INTRO,
                                pfExpChildren,
                                {conc},
                                true);
          }
        }
        // now, call expand definitions again on the result
        TrustNode texp = expandDefinitions(instance, cache, expandOnly, tpg);
        Node expanded = texp.isNull() ? instance : texp.getNode();
        cache[n] = n == expanded ? Node::null() : expanded;
        result.push(expanded);
        continue;
      }
      else if (!expandOnly)
      {
        // do not do any theory stuff if expandOnly is true

        theory::Theory* t = d_smt.getTheoryEngine()->theoryOf(node);

        Assert(t != NULL);
        TrustNode trn = t->expandDefinition(n);
        if (!trn.isNull())
        {
          node = trn.getNode();
          if (tpg != nullptr)
          {
            tpg->addRewriteStep(
                n, node, trn.getGenerator(), true, PfRule::THEORY_EXPAND_DEF);
          }
        }
        else
        {
          node = n;
        }
      }

      // the partial functions can fall through, in which case we still
      // consider their children
      worklist.push(std::make_tuple(
          Node(n), node, true));  // Original and rewritten result

      for (size_t i = 0; i < node.getNumChildren(); ++i)
      {
        worklist.push(
            std::make_tuple(node[i],
                            node[i],
                            false));  // Rewrite the children of the result only
      }
    }
    else
    {
      // Working upwards
      // Reconstruct the node from it's (now rewritten) children on the stack

      Debug("expand") << "cons : " << node << std::endl;
      if (node.getNumChildren() > 0)
      {
        // cout << "cons : " << node << std::endl;
        NodeBuilder<> nb(node.getKind());
        if (node.getMetaKind() == metakind::PARAMETERIZED)
        {
          Debug("expand") << "op   : " << node.getOperator() << std::endl;
          // cout << "op   : " << node.getOperator() << std::endl;
          nb << node.getOperator();
        }
        for (size_t i = 0, nchild = node.getNumChildren(); i < nchild; ++i)
        {
          Assert(!result.empty());
          Node expanded = result.top();
          result.pop();
          // cout << "exchld : " << expanded << std::endl;
          Debug("expand") << "exchld : " << expanded << std::endl;
          nb << expanded;
        }
        node = nb;
      }
      // Only cache once all subterms are expanded
      cache[n] = n == node ? Node::null() : node;
      result.push(node);
    }
  } while (!worklist.empty());

  AlwaysAssert(result.size() == 1);

  Node res = result.top();

  if (res == orig)
  {
    return TrustNode::null();
  }
  return TrustNode::mkTrustRewrite(orig, res, tpg);
}

void ExpandDefs::expandAssertions(AssertionPipeline& assertions,
                                  bool expandOnly)
{
  Chat() << "expanding definitions in assertions..." << std::endl;
  Trace("exp-defs") << "ExpandDefs::simplify(): expanding definitions"
                    << std::endl;
  TimerStat::CodeTimer codeTimer(d_smtStats.d_definitionExpansionTime);
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  for (size_t i = 0, nasserts = assertions.size(); i < nasserts; ++i)
  {
    Node assert = assertions[i];
    // notice we call this method with only one value of expandOnly currently,
    // hence we maintain only a single set of proof steps in d_tpg.
    TrustNode expd = expandDefinitions(assert, cache, expandOnly, d_tpg.get());
    if (!expd.isNull())
    {
      Trace("exp-defs") << "ExpandDefs::expandAssertions: " << assert << " -> "
                        << expd.getNode() << std::endl;
      assertions.replaceTrusted(i, expd);
    }
  }
}

void ExpandDefs::setProofNodeManager(ProofNodeManager* pnm)
{
  if (d_tpg == nullptr)
  {
    d_tpg.reset(new TConvProofGenerator(pnm,
                                        d_smt.getUserContext(),
                                        TConvPolicy::FIXPOINT,
                                        TConvCachePolicy::NEVER,
                                        "ExpandDefs::TConvProofGenerator",
                                        nullptr,
                                        true));
  }
}

}  // namespace smt
}  // namespace CVC4
