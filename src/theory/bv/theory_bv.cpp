/*********************                                                        */
/*! \file theory_bv.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Andrew Reynolds, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/bv/theory_bv.h"

#include "expr/node_algorithm.h"
#include "options/bv_options.h"
#include "options/smt_options.h"
#include "proof/proof_manager.h"
#include "proof/theory_proof.h"
#include "smt/smt_statistics_registry.h"
#include "theory/bv/abstraction.h"
#include "theory/bv/bv_eager_solver.h"
#include "theory/bv/bv_subtheory_algebraic.h"
#include "theory/bv/bv_subtheory_bitblast.h"
#include "theory/bv/bv_subtheory_core.h"
#include "theory/bv/bv_subtheory_inequality.h"
#include "theory/bv/slicer.h"
#include "theory/bv/theory_bv_rewrite_rules_normalization.h"
#include "theory/bv/theory_bv_rewrite_rules_simplification.h"
#include "theory/bv/theory_bv_rewriter.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/ext_theory.h"
#include "theory/theory_model.h"
#include "theory/valuation.h"

using namespace CVC4::context;
using namespace CVC4::theory::bv::utils;
using namespace std;

namespace CVC4 {
namespace theory {
namespace bv {

TheoryBV::TheoryBV(context::Context* c,
                   context::UserContext* u,
                   OutputChannel& out,
                   Valuation valuation,
                   const LogicInfo& logicInfo,
                   std::string name)
    : Theory(THEORY_BV, c, u, out, valuation, logicInfo, name),
      d_context(c),
      d_alreadyPropagatedSet(c),
      d_sharedTermsSet(c),
      d_subtheories(),
      d_subtheoryMap(),
      d_statistics(),
      d_staticLearnCache(),
      d_BVDivByZero(),
      d_BVRemByZero(),
      d_lemmasAdded(c, false),
      d_conflict(c, false),
      d_invalidateModelCache(c, true),
      d_literalsToPropagate(c),
      d_literalsToPropagateIndex(c, 0),
      d_propagatedBy(c),
      d_eagerSolver(),
      d_abstractionModule(new AbstractionModule(getStatsPrefix(THEORY_BV))),
      d_isCoreTheory(false),
      d_calledPreregister(false),
      d_needsLastCallCheck(false),
      d_extf_range_infer(u),
      d_extf_collapse_infer(u)
{
  setupExtTheory();
  getExtTheory()->addFunctionKind(kind::BITVECTOR_TO_NAT);
  getExtTheory()->addFunctionKind(kind::INT_TO_BITVECTOR);
  if (options::bitblastMode() == options::BitblastMode::EAGER)
  {
    d_eagerSolver.reset(new EagerBitblastSolver(c, this));
    return;
  }

  if (options::bitvectorEqualitySolver() && !options::proof())
  {
    d_subtheories.emplace_back(new CoreSolver(c, this));
    d_subtheoryMap[SUB_CORE] = d_subtheories.back().get();
  }

  if (options::bitvectorInequalitySolver() && !options::proof())
  {
    d_subtheories.emplace_back(new InequalitySolver(c, u, this));
    d_subtheoryMap[SUB_INEQUALITY] = d_subtheories.back().get();
  }

  if (options::bitvectorAlgebraicSolver() && !options::proof())
  {
    d_subtheories.emplace_back(new AlgebraicSolver(c, this));
    d_subtheoryMap[SUB_ALGEBRAIC] = d_subtheories.back().get();
  }

  BitblastSolver* bb_solver = new BitblastSolver(c, this);
  if (options::bvAbstraction())
  {
    bb_solver->setAbstraction(d_abstractionModule.get());
  }
  d_subtheories.emplace_back(bb_solver);
  d_subtheoryMap[SUB_BITBLAST] = bb_solver;
}

TheoryBV::~TheoryBV() {}

void TheoryBV::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  if (options::bitblastMode() == options::BitblastMode::EAGER)
  {
    return;
  }
  if (options::bitvectorEqualitySolver()) {
    dynamic_cast<CoreSolver*>(d_subtheoryMap[SUB_CORE])->setMasterEqualityEngine(eq);
  }
}

void TheoryBV::spendResource(ResourceManager::Resource r)
{
  getOutputChannel().spendResource(r);
}

TheoryBV::Statistics::Statistics():
  d_avgConflictSize("theory::bv::AvgBVConflictSize"),
  d_solveSubstitutions("theory::bv::NumSolveSubstitutions", 0),
  d_solveTimer("theory::bv::solveTimer"),
  d_numCallsToCheckFullEffort("theory::bv::NumFullCheckCalls", 0),
  d_numCallsToCheckStandardEffort("theory::bv::NumStandardCheckCalls", 0),
  d_weightComputationTimer("theory::bv::weightComputationTimer"),
  d_numMultSlice("theory::bv::NumMultSliceApplied", 0)
{
  smtStatisticsRegistry()->registerStat(&d_avgConflictSize);
  smtStatisticsRegistry()->registerStat(&d_solveSubstitutions);
  smtStatisticsRegistry()->registerStat(&d_solveTimer);
  smtStatisticsRegistry()->registerStat(&d_numCallsToCheckFullEffort);
  smtStatisticsRegistry()->registerStat(&d_numCallsToCheckStandardEffort);
  smtStatisticsRegistry()->registerStat(&d_weightComputationTimer);
  smtStatisticsRegistry()->registerStat(&d_numMultSlice);
}

TheoryBV::Statistics::~Statistics() {
  smtStatisticsRegistry()->unregisterStat(&d_avgConflictSize);
  smtStatisticsRegistry()->unregisterStat(&d_solveSubstitutions);
  smtStatisticsRegistry()->unregisterStat(&d_solveTimer);
  smtStatisticsRegistry()->unregisterStat(&d_numCallsToCheckFullEffort);
  smtStatisticsRegistry()->unregisterStat(&d_numCallsToCheckStandardEffort);
  smtStatisticsRegistry()->unregisterStat(&d_weightComputationTimer);
  smtStatisticsRegistry()->unregisterStat(&d_numMultSlice);
}

Node TheoryBV::getBVDivByZero(Kind k, unsigned width) {
  NodeManager* nm = NodeManager::currentNM();
  if (k == kind::BITVECTOR_UDIV) {
    if (d_BVDivByZero.find(width) == d_BVDivByZero.end()) {
      // lazily create the function symbols
      ostringstream os;
      os << "BVUDivByZero_" << width;
      Node divByZero = nm->mkSkolem(os.str(),
                                    nm->mkFunctionType(nm->mkBitVectorType(width), nm->mkBitVectorType(width)),
                                    "partial bvudiv", NodeManager::SKOLEM_EXACT_NAME);
      d_BVDivByZero[width] = divByZero;
    }
    return d_BVDivByZero[width];
  }
  else if (k == kind::BITVECTOR_UREM) {
    if (d_BVRemByZero.find(width) == d_BVRemByZero.end()) {
      ostringstream os;
      os << "BVURemByZero_" << width;
      Node divByZero = nm->mkSkolem(os.str(),
                                    nm->mkFunctionType(nm->mkBitVectorType(width), nm->mkBitVectorType(width)),
                                    "partial bvurem", NodeManager::SKOLEM_EXACT_NAME);
      d_BVRemByZero[width] = divByZero;
    }
    return d_BVRemByZero[width];
  }

  Unreachable();
}

void TheoryBV::finishInit()
{
  // these kinds are semi-evaluated in getModelValue (applications of this
  // kind are treated as variables)
  TheoryModel* tm = d_valuation.getModel();
  Assert(tm != nullptr);
  tm->setSemiEvaluatedKind(kind::BITVECTOR_ACKERMANNIZE_UDIV);
  tm->setSemiEvaluatedKind(kind::BITVECTOR_ACKERMANNIZE_UREM);
}

Node TheoryBV::expandDefinition(Node node)
{
  Debug("bitvector-expandDefinition") << "TheoryBV::expandDefinition(" << node << ")" << std::endl;

  switch (node.getKind()) {
  case kind::BITVECTOR_SDIV:
  case kind::BITVECTOR_SREM:
  case kind::BITVECTOR_SMOD:
    return TheoryBVRewriter::eliminateBVSDiv(node);
    break;

  case kind::BITVECTOR_UDIV:
  case kind::BITVECTOR_UREM: {
    NodeManager* nm = NodeManager::currentNM();
    unsigned width = node.getType().getBitVectorSize();

    if (options::bitvectorDivByZeroConst()) {
      Kind kind = node.getKind() == kind::BITVECTOR_UDIV ? kind::BITVECTOR_UDIV_TOTAL : kind::BITVECTOR_UREM_TOTAL;
      return nm->mkNode(kind, node[0], node[1]);
    }

    TNode num = node[0], den = node[1];
    Node den_eq_0 = nm->mkNode(kind::EQUAL, den, utils::mkZero(width));
    Node divTotalNumDen = nm->mkNode(node.getKind() == kind::BITVECTOR_UDIV ? kind::BITVECTOR_UDIV_TOTAL :
				     kind::BITVECTOR_UREM_TOTAL, num, den);
    Node divByZero = getBVDivByZero(node.getKind(), width);
    Node divByZeroNum = nm->mkNode(kind::APPLY_UF, divByZero, num);
    node = nm->mkNode(kind::ITE, den_eq_0, divByZeroNum, divTotalNumDen);
    return node;
  }
    break;

  default:
    return node;
    break;
  }

  Unreachable();
}

void TheoryBV::preRegisterTerm(TNode node) {
  d_calledPreregister = true;
  Debug("bitvector-preregister") << "TheoryBV::preRegister(" << node << ")" << std::endl;

  if (options::bitblastMode() == options::BitblastMode::EAGER)
  {
    // the aig bit-blaster option is set heuristically
    // if bv abstraction is used
    if (!d_eagerSolver->isInitialized())
    {
      d_eagerSolver->initialize();
    }

    if (node.getKind() == kind::BITVECTOR_EAGER_ATOM)
    {
      Node formula = node[0];
      d_eagerSolver->assertFormula(formula);
    }
    return;
  }

  for (unsigned i = 0; i < d_subtheories.size(); ++i) {
    d_subtheories[i]->preRegister(node);
  }
  
  // AJR : equality solver currently registers all terms to ExtTheory, if we want a lazy reduction without the bv equality solver, need to call this
  //getExtTheory()->registerTermRec( node );
}

void TheoryBV::sendConflict() {
  Assert(d_conflict);
  if (d_conflictNode.isNull()) {
    return;
  } else {
    Debug("bitvector") << indent() << "TheoryBV::check(): conflict " << d_conflictNode << std::endl;
    d_out->conflict(d_conflictNode);
    d_statistics.d_avgConflictSize.addEntry(d_conflictNode.getNumChildren());
    d_conflictNode = Node::null();
  }
}

void TheoryBV::checkForLemma(TNode fact)
{
  if (fact.getKind() == kind::EQUAL)
  {
    NodeManager* nm = NodeManager::currentNM();
    if (fact[0].getKind() == kind::BITVECTOR_UREM_TOTAL)
    {
      TNode urem = fact[0];
      TNode result = fact[1];
      TNode divisor = urem[1];
      Node result_ult_div = nm->mkNode(kind::BITVECTOR_ULT, result, divisor);
      Node divisor_eq_0 =
          nm->mkNode(kind::EQUAL, divisor, mkZero(getSize(divisor)));
      Node split = nm->mkNode(
          kind::OR, divisor_eq_0, nm->mkNode(kind::NOT, fact), result_ult_div);
      lemma(split);
    }
    if (fact[1].getKind() == kind::BITVECTOR_UREM_TOTAL)
    {
      TNode urem = fact[1];
      TNode result = fact[0];
      TNode divisor = urem[1];
      Node result_ult_div = nm->mkNode(kind::BITVECTOR_ULT, result, divisor);
      Node divisor_eq_0 =
          nm->mkNode(kind::EQUAL, divisor, mkZero(getSize(divisor)));
      Node split = nm->mkNode(
          kind::OR, divisor_eq_0, nm->mkNode(kind::NOT, fact), result_ult_div);
      lemma(split);
    }
  }
}

void TheoryBV::check(Effort e)
{
  if (done() && e<Theory::EFFORT_FULL) {
    return;
  }
  
  //last call : do reductions on extended bitvector functions
  if (e == Theory::EFFORT_LAST_CALL) {
    std::vector<Node> nred = getExtTheory()->getActive();
    doExtfReductions(nred);
    return;
  }

  TimerStat::CodeTimer checkTimer(d_checkTime);
  Debug("bitvector") << "TheoryBV::check(" << e << ")" << std::endl;
  TimerStat::CodeTimer codeTimer(d_statistics.d_solveTimer);
  // we may be getting new assertions so the model cache may not be sound
  d_invalidateModelCache.set(true);
  // if we are using the eager solver
  if (options::bitblastMode() == options::BitblastMode::EAGER)
  {
    // this can only happen on an empty benchmark
    if (!d_eagerSolver->isInitialized()) {
      d_eagerSolver->initialize();
    }
    if (!Theory::fullEffort(e))
      return;

    std::vector<TNode> assertions;
    while (!done()) {
      TNode fact = get().d_assertion;
      Assert(fact.getKind() == kind::BITVECTOR_EAGER_ATOM);
      assertions.push_back(fact);
      d_eagerSolver->assertFormula(fact[0]);
    }

    bool ok = d_eagerSolver->checkSat();
    if (!ok) {
      if (assertions.size() == 1) {
        d_out->conflict(assertions[0]);
        return;
      }
      Node conflict = utils::mkAnd(assertions);
      d_out->conflict(conflict);
      return;
    }
    return;
  }

  if (Theory::fullEffort(e)) {
    ++(d_statistics.d_numCallsToCheckFullEffort);
  } else {
    ++(d_statistics.d_numCallsToCheckStandardEffort);
  }
  // if we are already in conflict just return the conflict
  if (inConflict()) {
    sendConflict();
    return;
  }

  while (!done()) {
    TNode fact = get().d_assertion;

    checkForLemma(fact);

    for (unsigned i = 0; i < d_subtheories.size(); ++i) {
      d_subtheories[i]->assertFact(fact);
    }
  }

  bool ok = true;
  bool complete = false;
  for (unsigned i = 0; i < d_subtheories.size(); ++i) {
    Assert(!inConflict());
    ok = d_subtheories[i]->check(e);
    complete = d_subtheories[i]->isComplete();

    if (!ok) {
      // if we are in a conflict no need to check with other theories
      Assert(inConflict());
      sendConflict();
      return;
    }
    if (complete) {
      // if the last subtheory was complete we stop
      break;
    }
  }
  
  //check extended functions
  if (Theory::fullEffort(e)) {
    //do inferences (adds external lemmas)  TODO: this can be improved to add internal inferences
    std::vector< Node > nred;
    if( getExtTheory()->doInferences( 0, nred ) ){
      return;
    }
    d_needsLastCallCheck = false;
    if( !nred.empty() ){
      //other inferences involving bv2nat, int2bv
      if( options::bvAlgExtf() ){
        if( doExtfInferences( nred ) ){
          return;
        }
      }
      if( !options::bvLazyReduceExtf() ){
        if( doExtfReductions( nred ) ){
          return;
        }
      }else{     
        d_needsLastCallCheck = true;
      }
    }
  }
}

bool TheoryBV::doExtfInferences(std::vector<Node>& terms)
{
  NodeManager* nm = NodeManager::currentNM();
  bool sentLemma = false;
  eq::EqualityEngine* ee = getEqualityEngine();
  std::map<Node, Node> op_map;
  for (unsigned j = 0; j < terms.size(); j++)
  {
    TNode n = terms[j];
    Assert(n.getKind() == kind::BITVECTOR_TO_NAT
           || n.getKind() == kind::INT_TO_BITVECTOR);
    if (n.getKind() == kind::BITVECTOR_TO_NAT)
    {
      // range lemmas
      if (d_extf_range_infer.find(n) == d_extf_range_infer.end())
      {
        d_extf_range_infer.insert(n);
        unsigned bvs = n[0].getType().getBitVectorSize();
        Node min = nm->mkConst(Rational(0));
        Node max = nm->mkConst(Rational(Integer(1).multiplyByPow2(bvs)));
        Node lem = nm->mkNode(kind::AND,
                              nm->mkNode(kind::GEQ, n, min),
                              nm->mkNode(kind::LT, n, max));
        Trace("bv-extf-lemma")
            << "BV extf lemma (range) : " << lem << std::endl;
        d_out->lemma(lem);
        sentLemma = true;
      }
    }
    Node r = (ee && ee->hasTerm(n[0])) ? ee->getRepresentative(n[0]) : n[0];
    op_map[r] = n;
  }
  for (unsigned j = 0; j < terms.size(); j++)
  {
    TNode n = terms[j];
    Node r = (ee && ee->hasTerm(n[0])) ? ee->getRepresentative(n) : n;
    std::map<Node, Node>::iterator it = op_map.find(r);
    if (it != op_map.end())
    {
      Node parent = it->second;
      // Node cterm = parent[0]==n ? parent : nm->mkNode( parent.getOperator(),
      // n );
      Node cterm = parent[0].eqNode(n);
      Trace("bv-extf-lemma-debug")
          << "BV extf collapse based on : " << cterm << std::endl;
      if (d_extf_collapse_infer.find(cterm) == d_extf_collapse_infer.end())
      {
        d_extf_collapse_infer.insert(cterm);

        Node t = n[0];
        if (t.getType() == parent.getType())
        {
          if (n.getKind() == kind::INT_TO_BITVECTOR)
          {
            Assert(t.getType().isInteger());
            // congruent modulo 2^( bv width )
            unsigned bvs = n.getType().getBitVectorSize();
            Node coeff = nm->mkConst(Rational(Integer(1).multiplyByPow2(bvs)));
            Node k = nm->mkSkolem(
                "int_bv_cong", t.getType(), "for int2bv/bv2nat congruence");
            t = nm->mkNode(kind::PLUS, t, nm->mkNode(kind::MULT, coeff, k));
          }
          Node lem = parent.eqNode(t);

          if (parent[0] != n)
          {
            Assert(ee->areEqual(parent[0], n));
            lem = nm->mkNode(kind::IMPLIES, parent[0].eqNode(n), lem);
          }
          // this handles inferences of the form, e.g.:
          //   ((_ int2bv w) (bv2nat x)) == x (if x is bit-width w)
          //   (bv2nat ((_ int2bv w) x)) == x + k*2^w for some k
          Trace("bv-extf-lemma")
              << "BV extf lemma (collapse) : " << lem << std::endl;
          d_out->lemma(lem);
          sentLemma = true;
        }
      }
      Trace("bv-extf-lemma-debug")
          << "BV extf f collapse based on : " << cterm << std::endl;
    }
  }
  return sentLemma;
}

bool TheoryBV::doExtfReductions( std::vector< Node >& terms ) {
  std::vector< Node > nredr;
  if( getExtTheory()->doReductions( 0, terms, nredr ) ){
    return true;
  }
  Assert(nredr.empty());
  return false;
}

bool TheoryBV::needsCheckLastEffort() {
  return d_needsLastCallCheck;
}
bool TheoryBV::collectModelInfo(TheoryModel* m)
{
  Assert(!inConflict());
  if (options::bitblastMode() == options::BitblastMode::EAGER)
  {
    if (!d_eagerSolver->collectModelInfo(m, true))
    {
      return false;
    }
  }
  for (unsigned i = 0; i < d_subtheories.size(); ++i) {
    if (d_subtheories[i]->isComplete()) {
      return d_subtheories[i]->collectModelInfo(m, true);
    }
  }
  return true;
}

Node TheoryBV::getModelValue(TNode var) {
  Assert(!inConflict());
  for (unsigned i = 0; i < d_subtheories.size(); ++i) {
    if (d_subtheories[i]->isComplete()) {
      return d_subtheories[i]->getModelValue(var);
    }
  }
  Unreachable();
}

void TheoryBV::propagate(Effort e) {
  Debug("bitvector") << indent() << "TheoryBV::propagate()" << std::endl;
  if (options::bitblastMode() == options::BitblastMode::EAGER)
  {
    return;
  }

  if (inConflict()) {
    return;
  }

  // go through stored propagations
  bool ok = true;
  for (; d_literalsToPropagateIndex < d_literalsToPropagate.size() && ok; d_literalsToPropagateIndex = d_literalsToPropagateIndex + 1) {
    TNode literal = d_literalsToPropagate[d_literalsToPropagateIndex];
    // temporary fix for incremental bit-blasting
    if (d_valuation.isSatLiteral(literal)) {
      Debug("bitvector::propagate") << "TheoryBV:: propagating " << literal <<"\n";
      ok = d_out->propagate(literal);
    }
  }

  if (!ok) {
    Debug("bitvector::propagate") << indent() << "TheoryBV::propagate(): conflict from theory engine" << std::endl;
    setConflict();
  }
}


eq::EqualityEngine * TheoryBV::getEqualityEngine() {
  CoreSolver* core = (CoreSolver*)d_subtheoryMap[SUB_CORE];
  if( core ){
    return core->getEqualityEngine();
  }else{
    return NULL;
  }
}

bool TheoryBV::getCurrentSubstitution( int effort, std::vector< Node >& vars, std::vector< Node >& subs, std::map< Node, std::vector< Node > >& exp ) {
  eq::EqualityEngine * ee = getEqualityEngine();
  if( ee ){
    //get the constant equivalence classes
    bool retVal = false;
    for( unsigned i=0; i<vars.size(); i++ ){
      Node n = vars[i];
      if( ee->hasTerm( n ) ){
        Node nr = ee->getRepresentative( n );
        if( nr.isConst() ){
          subs.push_back( nr );
          exp[n].push_back( n.eqNode( nr ) );
          retVal = true;
        }else{
          subs.push_back( n );
        }
      }else{
        subs.push_back( n );
      }
    }
    //return true if the substitution is non-trivial
    return retVal;
  }
  return false;
}

int TheoryBV::getReduction(int effort, Node n, Node& nr)
{
  Trace("bv-ext") << "TheoryBV::checkExt : non-reduced : " << n << std::endl;
  if (n.getKind() == kind::BITVECTOR_TO_NAT)
  {
    nr = utils::eliminateBv2Nat(n);
    return -1;
  }
  else if (n.getKind() == kind::INT_TO_BITVECTOR)
  {
    nr = utils::eliminateInt2Bv(n);
    return -1;
  }
  return 0;
}

Theory::PPAssertStatus TheoryBV::ppAssert(TNode in,
                                          SubstitutionMap& outSubstitutions)
{
  switch (in.getKind())
  {
    case kind::EQUAL:
    {
      if (in[0].isVar() && isLegalElimination(in[0], in[1]))
      {
        ++(d_statistics.d_solveSubstitutions);
        outSubstitutions.addSubstitution(in[0], in[1]);
        return PP_ASSERT_STATUS_SOLVED;
      }
      if (in[1].isVar() && isLegalElimination(in[1], in[0]))
      {
        ++(d_statistics.d_solveSubstitutions);
        outSubstitutions.addSubstitution(in[1], in[0]);
        return PP_ASSERT_STATUS_SOLVED;
      }
      Node node = Rewriter::rewrite(in);
      if ((node[0].getKind() == kind::BITVECTOR_EXTRACT && node[1].isConst())
          || (node[1].getKind() == kind::BITVECTOR_EXTRACT
              && node[0].isConst()))
      {
        Node extract = node[0].isConst() ? node[1] : node[0];
        if (extract[0].isVar())
        {
          Node c = node[0].isConst() ? node[0] : node[1];

          unsigned high = utils::getExtractHigh(extract);
          unsigned low = utils::getExtractLow(extract);
          unsigned var_bitwidth = utils::getSize(extract[0]);
          std::vector<Node> children;

          if (low == 0)
          {
            Assert(high != var_bitwidth - 1);
            unsigned skolem_size = var_bitwidth - high - 1;
            Node skolem = utils::mkVar(skolem_size);
            children.push_back(skolem);
            children.push_back(c);
          }
          else if (high == var_bitwidth - 1)
          {
            unsigned skolem_size = low;
            Node skolem = utils::mkVar(skolem_size);
            children.push_back(c);
            children.push_back(skolem);
          }
          else
          {
            unsigned skolem1_size = low;
            unsigned skolem2_size = var_bitwidth - high - 1;
            Node skolem1 = utils::mkVar(skolem1_size);
            Node skolem2 = utils::mkVar(skolem2_size);
            children.push_back(skolem2);
            children.push_back(c);
            children.push_back(skolem1);
          }
          Node concat = utils::mkConcat(children);
          Assert(utils::getSize(concat) == utils::getSize(extract[0]));
          if (isLegalElimination(extract[0], concat))
          {
            outSubstitutions.addSubstitution(extract[0], concat);
            return PP_ASSERT_STATUS_SOLVED;
          }
        }
      }
    }
    break;
    case kind::BITVECTOR_ULT:
    case kind::BITVECTOR_SLT:
    case kind::BITVECTOR_ULE:
    case kind::BITVECTOR_SLE:

    default:
      // TODO other predicates
      break;
  }
  return PP_ASSERT_STATUS_UNSOLVED;
}

Node TheoryBV::ppRewrite(TNode t)
{
  Debug("bv-pp-rewrite") << "TheoryBV::ppRewrite " << t << "\n";
  Node res = t;
  if (options::bitwiseEq() && RewriteRule<BitwiseEq>::applies(t)) {
    Node result = RewriteRule<BitwiseEq>::run<false>(t);
    res = Rewriter::rewrite(result);
  } else if (d_isCoreTheory && t.getKind() == kind::EQUAL) {
    std::vector<Node> equalities;
    Slicer::splitEqualities(t, equalities);
    res = utils::mkAnd(equalities);
  } else if (RewriteRule<UltPlusOne>::applies(t)) {
    Node result = RewriteRule<UltPlusOne>::run<false>(t);
    res = Rewriter::rewrite(result);
  } else if( res.getKind() == kind::EQUAL &&
      ((res[0].getKind() == kind::BITVECTOR_PLUS &&
        RewriteRule<ConcatToMult>::applies(res[1])) ||
       (res[1].getKind() == kind::BITVECTOR_PLUS &&
	RewriteRule<ConcatToMult>::applies(res[0])))) {
    Node mult = RewriteRule<ConcatToMult>::applies(res[0])?
      RewriteRule<ConcatToMult>::run<false>(res[0]) :
      RewriteRule<ConcatToMult>::run<true>(res[1]);
    Node factor = mult[0];
    Node sum =  RewriteRule<ConcatToMult>::applies(res[0])? res[1] : res[0];
    Node new_eq = NodeManager::currentNM()->mkNode(kind::EQUAL, sum, mult);
    Node rewr_eq = RewriteRule<SolveEq>::run<true>(new_eq);
    if (rewr_eq[0].isVar() || rewr_eq[1].isVar()){
      res = Rewriter::rewrite(rewr_eq);
    } else {
      res = t;
    }
  } else if (RewriteRule<SignExtendEqConst>::applies(t)) {
    res = RewriteRule<SignExtendEqConst>::run<false>(t);
  } else if (RewriteRule<ZeroExtendEqConst>::applies(t)) {
    res = RewriteRule<ZeroExtendEqConst>::run<false>(t);
  }
  else if (RewriteRule<NormalizeEqPlusNeg>::applies(t))
  {
    res = RewriteRule<NormalizeEqPlusNeg>::run<false>(t);
  }

  // if(t.getKind() == kind::EQUAL &&
  //    ((t[0].getKind() == kind::BITVECTOR_MULT && t[1].getKind() ==
  //    kind::BITVECTOR_PLUS) ||
  //     (t[1].getKind() == kind::BITVECTOR_MULT && t[0].getKind() ==
  //     kind::BITVECTOR_PLUS))) {
  //   // if we have an equality between a multiplication and addition
  //   // try to express multiplication in terms of addition
  //   Node mult = t[0].getKind() == kind::BITVECTOR_MULT? t[0] : t[1];
  //   Node add = t[0].getKind() == kind::BITVECTOR_PLUS? t[0] : t[1];
  //   if (RewriteRule<MultSlice>::applies(mult)) {
  //     Node new_mult = RewriteRule<MultSlice>::run<false>(mult);
  //     Node new_eq =
  //     Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::EQUAL,
  //     new_mult, add));

  //     // the simplification can cause the formula to blow up
  //     // only apply if formula reduced
  //     if (d_subtheoryMap.find(SUB_BITBLAST) != d_subtheoryMap.end()) {
  //       BitblastSolver* bv = (BitblastSolver*)d_subtheoryMap[SUB_BITBLAST];
  //       uint64_t old_size = bv->computeAtomWeight(t);
  //       Assert (old_size);
  //       uint64_t new_size = bv->computeAtomWeight(new_eq);
  //       double ratio = ((double)new_size)/old_size;
  //       if (ratio <= 0.4) {
  //         ++(d_statistics.d_numMultSlice);
  //         return new_eq;
  //       }
  //     }

  //     if (new_eq.getKind() == kind::CONST_BOOLEAN) {
  //       ++(d_statistics.d_numMultSlice);
  //       return new_eq;
  //     }
  //   }
  // }

  if (options::bvAbstraction() && t.getType().isBoolean()) {
    d_abstractionModule->addInputAtom(res);
  }
  Debug("bv-pp-rewrite") << "to   " << res << "\n";
  return res;
}

void TheoryBV::presolve() {
  Debug("bitvector") << "TheoryBV::presolve" << endl;
}

static int prop_count = 0;

bool TheoryBV::storePropagation(TNode literal, SubTheory subtheory)
{
  Debug("bitvector::propagate") << indent() << getSatContext()->getLevel() << " " << "TheoryBV::storePropagation(" << literal << ", " << subtheory << ")" << std::endl;
  prop_count++;

  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("bitvector::propagate") << indent() << "TheoryBV::storePropagation(" << literal << ", " << subtheory << "): already in conflict" << std::endl;
    return false;
  }

  // If propagated already, just skip
  PropagatedMap::const_iterator find = d_propagatedBy.find(literal);
  if (find != d_propagatedBy.end()) {
    return true;
  } else {
    bool polarity = literal.getKind() != kind::NOT;
    Node negatedLiteral = polarity ? literal.notNode() : (Node) literal[0];
    find = d_propagatedBy.find(negatedLiteral);
    if (find != d_propagatedBy.end() && (*find).second != subtheory) {
      // Safe to ignore this one, subtheory should produce a conflict
      return true;
    }

    d_propagatedBy[literal] = subtheory;
  }

  // Propagate differs depending on the subtheory
  // * bitblaster needs to be left alone until it's done, otherwise it doesn't
  //   know how to explain
  // * equality engine can propagate eagerly
  // TODO(2348): Determine if ok should be set by propagate. If not, remove ok.
  constexpr bool ok = true;
  if (subtheory == SUB_CORE) {
    d_out->propagate(literal);
    if (!ok) {
      setConflict();
    }
  } else {
    d_literalsToPropagate.push_back(literal);
  }
  return ok;

}/* TheoryBV::propagate(TNode) */


void TheoryBV::explain(TNode literal, std::vector<TNode>& assumptions) {
  Assert(wasPropagatedBySubtheory(literal));
  SubTheory sub = getPropagatingSubtheory(literal);
  d_subtheoryMap[sub]->explain(literal, assumptions);
}


Node TheoryBV::explain(TNode node) {
  Debug("bitvector::explain") << "TheoryBV::explain(" << node << ")" << std::endl;
  std::vector<TNode> assumptions;

  // Ask for the explanation
  explain(node, assumptions);
  // this means that it is something true at level 0
  if (assumptions.size() == 0) {
    return utils::mkTrue();
  }
  // return the explanation
  Node explanation = utils::mkAnd(assumptions);
  Debug("bitvector::explain") << "TheoryBV::explain(" << node << ") => " << explanation << std::endl;
  Debug("bitvector::explain") << "TheoryBV::explain done. \n";
  return explanation;
}


void TheoryBV::addSharedTerm(TNode t) {
  Debug("bitvector::sharing") << indent() << "TheoryBV::addSharedTerm(" << t << ")" << std::endl;
  d_sharedTermsSet.insert(t);
  if (options::bitvectorEqualitySolver()) {
    for (unsigned i = 0; i < d_subtheories.size(); ++i) {
      d_subtheories[i]->addSharedTerm(t);
    }
  }
}


EqualityStatus TheoryBV::getEqualityStatus(TNode a, TNode b)
{
  if (options::bitblastMode() == options::BitblastMode::EAGER)
    return EQUALITY_UNKNOWN;
  Assert(options::bitblastMode() == options::BitblastMode::LAZY);
  for (unsigned i = 0; i < d_subtheories.size(); ++i) {
    EqualityStatus status = d_subtheories[i]->getEqualityStatus(a, b);
    if (status != EQUALITY_UNKNOWN) {
      return status;
    }
  }
  return EQUALITY_UNKNOWN; ;
}


void TheoryBV::enableCoreTheorySlicer() {
  Assert(!d_calledPreregister);
  d_isCoreTheory = true;
  if (d_subtheoryMap.find(SUB_CORE) != d_subtheoryMap.end()) {
    CoreSolver* core = (CoreSolver*)d_subtheoryMap[SUB_CORE];
    core->enableSlicer();
  }
}


void TheoryBV::ppStaticLearn(TNode in, NodeBuilder<>& learned) {
  if(d_staticLearnCache.find(in) != d_staticLearnCache.end()){
    return;
  }
  d_staticLearnCache.insert(in);

  if (in.getKind() == kind::EQUAL) {
    if((in[0].getKind() == kind::BITVECTOR_PLUS && in[1].getKind() == kind::BITVECTOR_SHL) ||
       (in[1].getKind() == kind::BITVECTOR_PLUS && in[0].getKind() == kind::BITVECTOR_SHL)) {
      TNode p = in[0].getKind() == kind::BITVECTOR_PLUS ? in[0] : in[1];
      TNode s = in[0].getKind() == kind::BITVECTOR_PLUS ? in[1] : in[0];

      if(p.getNumChildren() == 2
         && p[0].getKind()  == kind::BITVECTOR_SHL
         && p[1].getKind()  == kind::BITVECTOR_SHL ){
        unsigned size = utils::getSize(s);
        Node one = utils::mkConst(size, 1u);
        if(s[0] == one && p[0][0] == one && p[1][0] == one){
          Node zero = utils::mkConst(size, 0u);
          TNode b = p[0];
          TNode c = p[1];
          // (s : 1 << S) = (b : 1 << B) + (c : 1 << C)
          Node b_eq_0 = b.eqNode(zero);
          Node c_eq_0 = c.eqNode(zero);
          Node b_eq_c = b.eqNode(c);

          Node dis = NodeManager::currentNM()->mkNode(
              kind::OR, b_eq_0, c_eq_0, b_eq_c);
          Node imp = in.impNode(dis);
          learned << imp;
        }
      }
    }
  }else if(in.getKind() == kind::AND){
    for(size_t i = 0, N = in.getNumChildren(); i < N; ++i){
      ppStaticLearn(in[i], learned);
    }
  }
}

bool TheoryBV::applyAbstraction(const std::vector<Node>& assertions, std::vector<Node>& new_assertions) {
  bool changed = d_abstractionModule->applyAbstraction(assertions, new_assertions);
  if (changed && options::bitblastMode() == options::BitblastMode::EAGER
      && options::bitvectorAig())
  {
    // disable AIG mode
    AlwaysAssert(!d_eagerSolver->isInitialized());
    d_eagerSolver->turnOffAig();
    d_eagerSolver->initialize();
  }
  return changed;
}

void TheoryBV::setProofLog(proof::BitVectorProof* bvp)
{
  if (options::bitblastMode() == options::BitblastMode::EAGER)
  {
    d_eagerSolver->setProofLog(bvp);
  }
  else
  {
    for( unsigned i=0; i< d_subtheories.size(); i++ ){
      d_subtheories[i]->setProofLog( bvp );
    }
  }
}

void TheoryBV::setConflict(Node conflict)
{
  if (options::bvAbstraction())
  {
    NodeManager* const nm = NodeManager::currentNM();
    Node new_conflict = d_abstractionModule->simplifyConflict(conflict);

    std::vector<Node> lemmas;
    lemmas.push_back(new_conflict);
    d_abstractionModule->generalizeConflict(new_conflict, lemmas);
    for (unsigned i = 0; i < lemmas.size(); ++i)
    {
      lemma(nm->mkNode(kind::NOT, lemmas[i]));
    }
  }
  d_conflict = true;
  d_conflictNode = conflict;
}

} /* namespace CVC4::theory::bv */
} /* namespace CVC4::theory */
} /* namespace CVC4 */
