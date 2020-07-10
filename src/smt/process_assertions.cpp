/*********************                                                        */
/*! \file process_assertions.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of module for processing assertions for an SMT engine.
 **/

#include "smt/process_assertions.h"

#include <stack>
#include <utility>

#include "expr/node_manager_attributes.h"
#include "options/arith_options.h"
#include "options/base_options.h"
#include "options/bv_options.h"
#include "options/proof_options.h"
#include "options/quantifiers_options.h"
#include "options/sep_options.h"
#include "options/smt_options.h"
#include "options/uf_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_registry.h"
#include "smt/defined_function.h"
#include "smt/smt_engine.h"
#include "theory/logic_info.h"
#include "theory/quantifiers/fun_def_process.h"
#include "theory/theory_engine.h"

using namespace CVC4::preprocessing;
using namespace CVC4::theory;
using namespace CVC4::kind;

namespace CVC4 {
namespace smt {

/** Useful for counting the number of recursive calls. */
class ScopeCounter
{
 public:
  ScopeCounter(unsigned& d) : d_depth(d) { ++d_depth; }
  ~ScopeCounter() { --d_depth; }

 private:
  unsigned& d_depth;
};

ProcessAssertions::ProcessAssertions(SmtEngine& smt, ResourceManager& rm)
    : d_smt(smt),
      d_resourceManager(rm),
      d_preprocessingPassContext(nullptr),
      d_fmfRecFunctionsDefined(nullptr)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_fmfRecFunctionsDefined = new (true) NodeList(d_smt.getUserContext());
}

ProcessAssertions::~ProcessAssertions()
{
  d_fmfRecFunctionsDefined->deleteSelf();
}

void ProcessAssertions::finishInit(PreprocessingPassContext* pc)
{
  Assert(d_preprocessingPassContext == nullptr);
  d_preprocessingPassContext = pc;

  PreprocessingPassRegistry& ppReg = PreprocessingPassRegistry::getInstance();
  // TODO: this will likely change when we add support for actually assembling
  // preprocessing pipelines. For now, we just create an instance of each
  // available preprocessing pass.
  std::vector<std::string> passNames = ppReg.getAvailablePasses();
  for (const std::string& passName : passNames)
  {
    d_passes[passName].reset(
        ppReg.createPass(d_preprocessingPassContext, passName));
  }
}

void ProcessAssertions::cleanup() { d_passes.clear(); }

void ProcessAssertions::spendResource(ResourceManager::Resource r)
{
  d_resourceManager.spendResource(r);
}

bool ProcessAssertions::apply(AssertionPipeline& assertions)
{
  Assert(d_preprocessingPassContext != nullptr);
  // Dump the assertions
  dumpAssertions("pre-everything", assertions);

  Trace("smt-proc") << "ProcessAssertions::processAssertions() begin" << endl;
  Trace("smt") << "ProcessAssertions::processAssertions()" << endl;

  Debug("smt") << "#Assertions : " << assertions.size() << endl;
  Debug("smt") << "#Assumptions: " << assertions.getNumAssumptions() << endl;

  if (assertions.size() == 0)
  {
    // nothing to do
    return true;
  }

  SubstitutionMap& top_level_substs =
      d_preprocessingPassContext->getTopLevelSubstitutions();

  if (options::bvGaussElim())
  {
    d_passes["bv-gauss"]->apply(&assertions);
  }

  // Add dummy assertion in last position - to be used as a
  // placeholder for any new assertions to get added
  assertions.push_back(d_true);
  // any assertions added beyond realAssertionsEnd must NOT affect the
  // equisatisfiability
  assertions.updateRealAssertionsEnd();

  // Assertions are NOT guaranteed to be rewritten by this point

  Trace("smt-proc")
      << "ProcessAssertions::processAssertions() : pre-definition-expansion"
      << endl;
  dumpAssertions("pre-definition-expansion", assertions);
  {
    Chat() << "expanding definitions..." << endl;
    Trace("simplify") << "ProcessAssertions::simplify(): expanding definitions"
                      << endl;
    TimerStat::CodeTimer codeTimer(d_smt.d_stats->d_definitionExpansionTime);
    unordered_map<Node, Node, NodeHashFunction> cache;
    for (size_t i = 0, nasserts = assertions.size(); i < nasserts; ++i)
    {
      assertions.replace(i, expandDefinitions(assertions[i], cache));
    }
  }
  Trace("smt-proc")
      << "ProcessAssertions::processAssertions() : post-definition-expansion"
      << endl;
  dumpAssertions("post-definition-expansion", assertions);

  // save the assertions now
  THEORY_PROOF(
      for (size_t i = 0, nasserts = assertions.size(); i < nasserts; ++i) {
        ProofManager::currentPM()->addAssertion(assertions[i].toExpr());
      });

  Debug("smt") << " assertions     : " << assertions.size() << endl;

  if (options::globalNegate())
  {
    // global negation of the formula
    d_passes["global-negate"]->apply(&assertions);
    d_smt.d_globalNegation = !d_smt.d_globalNegation;
  }

  if (options::nlExtPurify())
  {
    d_passes["nl-ext-purify"]->apply(&assertions);
  }

  if (options::solveRealAsInt())
  {
    d_passes["real-to-int"]->apply(&assertions);
  }

  if (options::solveIntAsBV() > 0)
  {
    d_passes["int-to-bv"]->apply(&assertions);
  }

  if (options::ackermann())
  {
    d_passes["ackermann"]->apply(&assertions);
  }

  if (options::bvAbstraction())
  {
    d_passes["bv-abstraction"]->apply(&assertions);
  }

  Debug("smt") << " assertions     : " << assertions.size() << endl;

  bool noConflict = true;

  if (options::extRewPrep())
  {
    d_passes["ext-rew-pre"]->apply(&assertions);
  }

  // Unconstrained simplification
  if (options::unconstrainedSimp())
  {
    d_passes["rewrite"]->apply(&assertions);
    d_passes["unconstrained-simplifier"]->apply(&assertions);
  }

  if (options::bvIntroducePow2())
  {
    d_passes["bv-intro-pow2"]->apply(&assertions);
  }

  // Since this pass is not robust for the information tracking necessary for
  // unsat cores, it's only applied if we are not doing unsat core computation
  if (!options::unsatCores())
  {
    d_passes["apply-substs"]->apply(&assertions);
  }

  // Assertions MUST BE guaranteed to be rewritten by this point
  d_passes["rewrite"]->apply(&assertions);

  // Lift bit-vectors of size 1 to bool
  if (options::bitvectorToBool())
  {
    d_passes["bv-to-bool"]->apply(&assertions);
  }
  if (options::solveBVAsInt() != options::SolveBVAsIntMode::OFF)
  {
    d_passes["bv-to-int"]->apply(&assertions);
  }

  // Convert non-top-level Booleans to bit-vectors of size 1
  if (options::boolToBitvector() != options::BoolToBVMode::OFF)
  {
    d_passes["bool-to-bv"]->apply(&assertions);
  }
  if (options::sepPreSkolemEmp())
  {
    d_passes["sep-skolem-emp"]->apply(&assertions);
  }

  if (d_smt.d_logic.isQuantified())
  {
    // remove rewrite rules, apply pre-skolemization to existential quantifiers
    d_passes["quantifiers-preprocess"]->apply(&assertions);
    if (options::macrosQuant())
    {
      // quantifiers macro expansion
      d_passes["quantifier-macros"]->apply(&assertions);
    }

    // fmf-fun : assume admissible functions, applying preprocessing reduction
    // to FMF
    if (options::fmfFunWellDefined())
    {
      quantifiers::FunDefFmf fdf;
      Assert(d_fmfRecFunctionsDefined != NULL);
      // must carry over current definitions (in case of incremental)
      for (context::CDList<Node>::const_iterator fit =
               d_fmfRecFunctionsDefined->begin();
           fit != d_fmfRecFunctionsDefined->end();
           ++fit)
      {
        Node f = (*fit);
        Assert(d_fmfRecFunctionsAbs.find(f) != d_fmfRecFunctionsAbs.end());
        TypeNode ft = d_fmfRecFunctionsAbs[f];
        fdf.d_sorts[f] = ft;
        std::map<Node, std::vector<Node>>::iterator fcit =
            d_fmfRecFunctionsConcrete.find(f);
        Assert(fcit != d_fmfRecFunctionsConcrete.end());
        for (const Node& fcc : fcit->second)
        {
          fdf.d_input_arg_inj[f].push_back(fcc);
        }
      }
      fdf.simplify(assertions.ref());
      // must store new definitions (in case of incremental)
      for (const Node& f : fdf.d_funcs)
      {
        d_fmfRecFunctionsAbs[f] = fdf.d_sorts[f];
        d_fmfRecFunctionsConcrete[f].clear();
        for (const Node& fcc : fdf.d_input_arg_inj[f])
        {
          d_fmfRecFunctionsConcrete[f].push_back(fcc);
        }
        d_fmfRecFunctionsDefined->push_back(f);
      }
    }
  }

  if (options::sortInference() || options::ufssFairnessMonotone())
  {
    d_passes["sort-inference"]->apply(&assertions);
  }

  if (options::pbRewrites())
  {
    d_passes["pseudo-boolean-processor"]->apply(&assertions);
  }

  // rephrasing normal inputs as sygus problems
  if (!d_smt.d_isInternalSubsolver)
  {
    if (options::sygusInference())
    {
      d_passes["sygus-infer"]->apply(&assertions);
    }
    else if (options::sygusRewSynthInput())
    {
      // do candidate rewrite rule synthesis
      d_passes["synth-rr"]->apply(&assertions);
    }
  }

  Trace("smt-proc") << "ProcessAssertions::processAssertions() : pre-simplify"
                    << endl;
  dumpAssertions("pre-simplify", assertions);
  Chat() << "simplifying assertions..." << endl;
  noConflict = simplifyAssertions(assertions);
  if (!noConflict)
  {
    ++(d_smt.d_stats->d_simplifiedToFalse);
  }
  Trace("smt-proc") << "ProcessAssertions::processAssertions() : post-simplify"
                    << endl;
  dumpAssertions("post-simplify", assertions);

  if (options::doStaticLearning())
  {
    d_passes["static-learning"]->apply(&assertions);
  }
  Debug("smt") << " assertions     : " << assertions.size() << endl;

  {
    d_smt.d_stats->d_numAssertionsPre += assertions.size();
    d_passes["ite-removal"]->apply(&assertions);
    // This is needed because when solving incrementally, removeITEs may
    // introduce skolems that were solved for earlier and thus appear in the
    // substitution map.
    d_passes["apply-substs"]->apply(&assertions);
    d_smt.d_stats->d_numAssertionsPost += assertions.size();
  }

  dumpAssertions("pre-repeat-simplify", assertions);
  if (options::repeatSimp())
  {
    Trace("smt-proc")
        << "ProcessAssertions::processAssertions() : pre-repeat-simplify"
        << endl;
    Chat() << "re-simplifying assertions..." << endl;
    ScopeCounter depth(d_simplifyAssertionsDepth);
    noConflict &= simplifyAssertions(assertions);
    if (noConflict)
    {
      // Need to fix up assertion list to maintain invariants:
      // Let Sk be the set of Skolem variables introduced by ITE's.  Let <_sk be
      // the order in which these variables were introduced during ite removal.
      // For each skolem variable sk, let iteExpr = iteMap(sk) be the ite expr
      // mapped to by sk.

      // cache for expression traversal
      unordered_map<Node, bool, NodeHashFunction> cache;

      IteSkolemMap& iskMap = assertions.getIteSkolemMap();
      // First, find all skolems that appear in the substitution map - their
      // associated iteExpr will need to be moved to the main assertion set
      set<TNode> skolemSet;
      SubstitutionMap::iterator pos = top_level_substs.begin();
      for (; pos != top_level_substs.end(); ++pos)
      {
        collectSkolems(iskMap, (*pos).first, skolemSet, cache);
        collectSkolems(iskMap, (*pos).second, skolemSet, cache);
      }
      // We need to ensure:
      // 1. iteExpr has the form (ite cond (sk = t) (sk = e))
      // 2. if some sk' in Sk appears in cond, t, or e, then sk' <_sk sk
      // If either of these is violated, we must add iteExpr as a proper
      // assertion
      IteSkolemMap::iterator it = iskMap.begin();
      IteSkolemMap::iterator iend = iskMap.end();
      NodeBuilder<> builder(AND);
      builder << assertions[assertions.getRealAssertionsEnd() - 1];
      vector<TNode> toErase;
      for (; it != iend; ++it)
      {
        if (skolemSet.find((*it).first) == skolemSet.end())
        {
          TNode iteExpr = assertions[(*it).second];
          if (iteExpr.getKind() == ITE && iteExpr[1].getKind() == EQUAL
              && iteExpr[1][0] == (*it).first && iteExpr[2].getKind() == EQUAL
              && iteExpr[2][0] == (*it).first)
          {
            cache.clear();
            bool bad =
                checkForBadSkolems(iskMap, iteExpr[0], (*it).first, cache);
            bad = bad
                  || checkForBadSkolems(
                         iskMap, iteExpr[1][1], (*it).first, cache);
            bad = bad
                  || checkForBadSkolems(
                         iskMap, iteExpr[2][1], (*it).first, cache);
            if (!bad)
            {
              continue;
            }
          }
        }
        // Move this iteExpr into the main assertions
        builder << assertions[(*it).second];
        assertions[(*it).second] = d_true;
        toErase.push_back((*it).first);
      }
      if (builder.getNumChildren() > 1)
      {
        while (!toErase.empty())
        {
          iskMap.erase(toErase.back());
          toErase.pop_back();
        }
        assertions[assertions.getRealAssertionsEnd() - 1] =
            Rewriter::rewrite(Node(builder));
      }
      // TODO(b/1256): For some reason this is needed for some benchmarks, such
      // as
      // QF_AUFBV/dwp_formulas/try5_small_difret_functions_dwp_tac.re_node_set_remove_at.il.dwp.smt2
      d_passes["ite-removal"]->apply(&assertions);
      d_passes["apply-substs"]->apply(&assertions);
    }
    Trace("smt-proc")
        << "ProcessAssertions::processAssertions() : post-repeat-simplify"
        << endl;
  }
  dumpAssertions("post-repeat-simplify", assertions);

  if (options::ufHo())
  {
    d_passes["ho-elim"]->apply(&assertions);
  }

  // begin: INVARIANT to maintain: no reordering of assertions or
  // introducing new ones

  Debug("smt") << " assertions     : " << assertions.size() << endl;

  Debug("smt") << "ProcessAssertions::processAssertions() POST SIMPLIFICATION"
               << endl;
  Debug("smt") << " assertions     : " << assertions.size() << endl;

  d_passes["theory-preprocess"]->apply(&assertions);

  if (options::bitblastMode() == options::BitblastMode::EAGER)
  {
    d_passes["bv-eager-atoms"]->apply(&assertions);
  }

  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() end" << endl;
  dumpAssertions("post-everything", assertions);

  return noConflict;
}

// returns false if simplification led to "false"
bool ProcessAssertions::simplifyAssertions(AssertionPipeline& assertions)
{
  spendResource(ResourceManager::Resource::PreprocessStep);
  Assert(d_smt.d_pendingPops == 0);
  try
  {
    ScopeCounter depth(d_simplifyAssertionsDepth);

    Trace("simplify") << "SmtEnginePrivate::simplify()" << endl;

    if (options::simplificationMode() != options::SimplificationMode::NONE)
    {
      if (!options::unsatCores() && !options::fewerPreprocessingHoles())
      {
        // Perform non-clausal simplification
        PreprocessingPassResult res =
            d_passes["non-clausal-simp"]->apply(&assertions);
        if (res == PreprocessingPassResult::CONFLICT)
        {
          return false;
        }
      }

      // We piggy-back off of the BackEdgesMap in the CircuitPropagator to
      // do the miplib trick.
      if (  // check that option is on
          options::arithMLTrick() &&
          // only useful in arith
          d_smt.d_logic.isTheoryEnabled(THEORY_ARITH) &&
          // we add new assertions and need this (in practice, this
          // restriction only disables miplib processing during
          // re-simplification, which we don't expect to be useful anyway)
          assertions.getRealAssertionsEnd() == assertions.size())
      {
        d_passes["miplib-trick"]->apply(&assertions);
      }
      else
      {
        Trace("simplify") << "SmtEnginePrivate::simplify(): "
                          << "skipping miplib pseudobooleans pass..." << endl;
      }
    }

    Debug("smt") << " assertions     : " << assertions.size() << endl;

    // before ppRewrite check if only core theory for BV theory
    d_smt.d_theoryEngine->staticInitializeBVOptions(assertions.ref());

    // Theory preprocessing
    bool doEarlyTheoryPp = !options::arithRewriteEq();
    if (doEarlyTheoryPp)
    {
      d_passes["theory-preprocess"]->apply(&assertions);
    }

    // ITE simplification
    if (options::doITESimp()
        && (d_simplifyAssertionsDepth <= 1 || options::doITESimpOnRepeat()))
    {
      PreprocessingPassResult res = d_passes["ite-simp"]->apply(&assertions);
      if (res == PreprocessingPassResult::CONFLICT)
      {
        Chat() << "...ITE simplification found unsat..." << endl;
        return false;
      }
    }

    Debug("smt") << " assertions     : " << assertions.size() << endl;

    // Unconstrained simplification
    if (options::unconstrainedSimp())
    {
      d_passes["unconstrained-simplifier"]->apply(&assertions);
    }

    if (options::repeatSimp()
        && options::simplificationMode() != options::SimplificationMode::NONE
        && !options::unsatCores() && !options::fewerPreprocessingHoles())
    {
      PreprocessingPassResult res =
          d_passes["non-clausal-simp"]->apply(&assertions);
      if (res == PreprocessingPassResult::CONFLICT)
      {
        return false;
      }
    }

    dumpAssertions("post-repeatsimp", assertions);
    Trace("smt") << "POST repeatSimp" << endl;
    Debug("smt") << " assertions     : " << assertions.size() << endl;
  }
  catch (TypeCheckingExceptionPrivate& tcep)
  {
    // Calls to this function should have already weeded out any
    // typechecking exceptions via (e.g.) ensureBoolean().  But a
    // theory could still create a new expression that isn't
    // well-typed, and we don't want the C++ runtime to abort our
    // process without any error notice.
    InternalError()
        << "A bad expression was produced.  Original exception follows:\n"
        << tcep;
  }
  return true;
}

void ProcessAssertions::dumpAssertions(const char* key,
                                       const AssertionPipeline& assertionList)
{
  if (Dump.isOn("assertions") && Dump.isOn(string("assertions:") + key))
  {
    // Push the simplified assertions to the dump output stream
    for (unsigned i = 0; i < assertionList.size(); ++i)
    {
      TNode n = assertionList[i];
      Dump("assertions") << AssertCommand(Expr(n.toExpr()));
    }
  }
}

Node ProcessAssertions::expandDefinitions(
    TNode n,
    unordered_map<Node, Node, NodeHashFunction>& cache,
    bool expandOnly)
{
  NodeManager* nm = d_smt.d_nodeManager;
  std::stack<std::tuple<Node, Node, bool>> worklist;
  std::stack<Node> result;
  worklist.push(std::make_tuple(Node(n), Node(n), false));
  // The worklist is made of triples, each is input / original node then the
  // output / rewritten node and finally a flag tracking whether the children
  // have been explored (i.e. if this is a downward or upward pass).

  do
  {
    spendResource(ResourceManager::Resource::PreprocessStep);

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
        SmtEngine::DefinedFunctionMap::const_iterator i =
            d_smt.d_definedFunctions->find(n);
        if (i != d_smt.d_definedFunctions->end())
        {
          Node f = (*i).second.getFormula();
          // must expand its definition
          Node fe = expandDefinitions(f, cache, expandOnly);
          // replacement must be closed
          if ((*i).second.getFormals().size() > 0)
          {
            result.push(
                nm->mkNode(LAMBDA,
                           nm->mkNode(BOUND_VAR_LIST, (*i).second.getFormals()),
                           fe));
            continue;
          }
          // don't bother putting in the cache
          result.push(fe);
          continue;
        }
        // don't bother putting in the cache
        result.push(n);
        continue;
      }

      // maybe it's in the cache
      unordered_map<Node, Node, NodeHashFunction>::iterator cacheHit =
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
      if (doExpand)
      {
        vector<Node> formals;
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
          SmtEngine::DefinedFunctionMap::const_iterator i =
              d_smt.d_definedFunctions->find(func);
          if (i == d_smt.d_definedFunctions->end())
          {
            throw TypeCheckingException(
                n.toExpr(),
                string("Undefined function: `") + func.toString() + "'");
          }
          DefinedFunction def = (*i).second;
          formals = def.getFormals();

          if (Debug.isOn("expand"))
          {
            Debug("expand") << "found: " << n << endl;
            Debug("expand") << " func: " << func << endl;
            string name = func.getAttribute(expr::VarNameAttr());
            Debug("expand") << "     : \"" << name << "\"" << endl;
          }
          if (Debug.isOn("expand"))
          {
            Debug("expand") << " defn: " << def.getFunction() << endl
                            << "       [";
            if (formals.size() > 0)
            {
              copy(formals.begin(),
                   formals.end() - 1,
                   ostream_iterator<Node>(Debug("expand"), ", "));
              Debug("expand") << formals.back();
            }
            Debug("expand") << "]" << endl
                            << "       " << def.getFunction().getType() << endl
                            << "       " << def.getFormula() << endl;
          }

          fm = def.getFormula();
        }

        Node instance = fm.substitute(formals.begin(),
                                      formals.end(),
                                      n.begin(),
                                      n.begin() + formals.size());
        Debug("expand") << "made : " << instance << endl;

        Node expanded = expandDefinitions(instance, cache, expandOnly);
        cache[n] = (n == expanded ? Node::null() : expanded);
        result.push(expanded);
        continue;
      }
      else if (!expandOnly)
      {
        // do not do any theory stuff if expandOnly is true

        theory::Theory* t = d_smt.d_theoryEngine->theoryOf(node);

        Assert(t != NULL);
        node = t->expandDefinition(n);
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

      Debug("expand") << "cons : " << node << endl;
      if (node.getNumChildren() > 0)
      {
        // cout << "cons : " << node << endl;
        NodeBuilder<> nb(node.getKind());
        if (node.getMetaKind() == metakind::PARAMETERIZED)
        {
          Debug("expand") << "op   : " << node.getOperator() << endl;
          // cout << "op   : " << node.getOperator() << endl;
          nb << node.getOperator();
        }
        for (size_t i = 0, nchild = node.getNumChildren(); i < nchild; ++i)
        {
          Assert(!result.empty());
          Node expanded = result.top();
          result.pop();
          // cout << "exchld : " << expanded << endl;
          Debug("expand") << "exchld : " << expanded << endl;
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

  return result.top();
}

void ProcessAssertions::collectSkolems(
    IteSkolemMap& iskMap,
    TNode n,
    set<TNode>& skolemSet,
    unordered_map<Node, bool, NodeHashFunction>& cache)
{
  unordered_map<Node, bool, NodeHashFunction>::iterator it;
  it = cache.find(n);
  if (it != cache.end())
  {
    return;
  }

  size_t sz = n.getNumChildren();
  if (sz == 0)
  {
    if (iskMap.find(n) != iskMap.end())
    {
      skolemSet.insert(n);
    }
    cache[n] = true;
    return;
  }

  size_t k = 0;
  for (; k < sz; ++k)
  {
    collectSkolems(iskMap, n[k], skolemSet, cache);
  }
  cache[n] = true;
}

bool ProcessAssertions::checkForBadSkolems(
    IteSkolemMap& iskMap,
    TNode n,
    TNode skolem,
    unordered_map<Node, bool, NodeHashFunction>& cache)
{
  unordered_map<Node, bool, NodeHashFunction>::iterator it;
  it = cache.find(n);
  if (it != cache.end())
  {
    return (*it).second;
  }

  size_t sz = n.getNumChildren();
  if (sz == 0)
  {
    IteSkolemMap::iterator iit = iskMap.find(n);
    bool bad = false;
    if (iit != iskMap.end())
    {
      if (!((*iit).first < n))
      {
        bad = true;
      }
    }
    cache[n] = bad;
    return bad;
  }

  size_t k = 0;
  for (; k < sz; ++k)
  {
    if (checkForBadSkolems(iskMap, n[k], skolem, cache))
    {
      cache[n] = true;
      return true;
    }
  }

  cache[n] = false;
  return false;
}

}  // namespace smt
}  // namespace CVC4
