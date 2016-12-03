/*********************                                                        */
/*! \file theory_bv.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Tim King, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/bv/theory_bv.h"

#include "options/bv_options.h"
#include "options/smt_options.h"
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
#include "theory/theory_model.h"
#include "proof/theory_proof.h"
#include "proof/proof_manager.h"
#include "theory/valuation.h"

using namespace CVC4::context;
using namespace CVC4::theory::bv::utils;
using namespace std;

namespace CVC4 {
namespace theory {
namespace bv {

TheoryBV::TheoryBV(context::Context* c, context::UserContext* u,
                   OutputChannel& out, Valuation valuation,
                   const LogicInfo& logicInfo, std::string name)
  : Theory(THEORY_BV, c, u, out, valuation, logicInfo, name),
    d_context(c),
    d_alreadyPropagatedSet(c),
    d_sharedTermsSet(c),
    d_subtheories(),
    d_subtheoryMap(),
    d_statistics(getFullInstanceName()),
    d_staticLearnCache(),
    d_BVDivByZero(),
    d_BVRemByZero(),
    d_funcToArgs(),
    d_funcToSkolem(u),
    d_lemmasAdded(c, false),
    d_conflict(c, false),
    d_invalidateModelCache(c, true),
    d_literalsToPropagate(c),
    d_literalsToPropagateIndex(c, 0),
    d_propagatedBy(c),
    d_eagerSolver(NULL),
    d_abstractionModule(new AbstractionModule(getFullInstanceName())),
    d_isCoreTheory(false),
    d_calledPreregister(false),
    d_needsLastCallCheck(false),
    d_extf_range_infer(u),
    d_extf_collapse_infer(u)
{
  d_extt = new ExtTheory( this );
  d_extt->addFunctionKind( kind::BITVECTOR_TO_NAT );
  d_extt->addFunctionKind( kind::INT_TO_BITVECTOR );

  if (options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER) {
    d_eagerSolver = new EagerBitblastSolver(this);
    return;
  }

  if (options::bitvectorEqualitySolver()) {
    SubtheorySolver* core_solver = new CoreSolver(c, this);
    d_subtheories.push_back(core_solver);
    d_subtheoryMap[SUB_CORE] = core_solver;
  }

  if (options::bitvectorInequalitySolver()) {
    SubtheorySolver* ineq_solver = new InequalitySolver(c, u, this);
    d_subtheories.push_back(ineq_solver);
    d_subtheoryMap[SUB_INEQUALITY] = ineq_solver;
  }

  if (options::bitvectorAlgebraicSolver()) {
    SubtheorySolver* alg_solver = new AlgebraicSolver(c, this);
    d_subtheories.push_back(alg_solver);
    d_subtheoryMap[SUB_ALGEBRAIC] = alg_solver;
  }

  BitblastSolver* bb_solver = new BitblastSolver(c, this);
  if (options::bvAbstraction()) {
    bb_solver->setAbstraction(d_abstractionModule);
  }
  d_subtheories.push_back(bb_solver);
  d_subtheoryMap[SUB_BITBLAST] = bb_solver;
}

TheoryBV::~TheoryBV() {
  if (d_eagerSolver) {
    delete d_eagerSolver;
  }
  for (unsigned i = 0; i < d_subtheories.size(); ++i) {
    delete d_subtheories[i];
  }
  delete d_abstractionModule;
  delete d_extt;
}

void TheoryBV::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  if (options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER) {
    return;
  }
  if (options::bitvectorEqualitySolver()) {
    dynamic_cast<CoreSolver*>(d_subtheoryMap[SUB_CORE])->setMasterEqualityEngine(eq);
  }
}

void TheoryBV::spendResource(unsigned ammount) throw(UnsafeInterruptException) {
  getOutputChannel().spendResource(ammount);
}

TheoryBV::Statistics::Statistics(const std::string &name):
  d_avgConflictSize(name + "theory::bv::AvgBVConflictSize"),
  d_solveSubstitutions(name + "theory::bv::NumberOfSolveSubstitutions", 0),
  d_solveTimer(name + "theory::bv::solveTimer"),
  d_numCallsToCheckFullEffort(name + "theory::bv::NumberOfFullCheckCalls", 0),
  d_numCallsToCheckStandardEffort(name + "theory::bv::NumberOfStandardCheckCalls", 0),
  d_weightComputationTimer(name + "theory::bv::weightComputationTimer"),
  d_numMultSlice(name + "theory::bv::NumMultSliceApplied", 0)
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


void TheoryBV::collectFunctionSymbols(TNode term, TNodeSet& seen) {
  if (seen.find(term) != seen.end())
    return;
  if (term.getKind() == kind::APPLY_UF) {
    TNode func = term.getOperator();
    storeFunction(func, term);
  } else if (term.getKind() == kind::SELECT) {
    TNode func = term[0];
    storeFunction(func, term);
  } else if (term.getKind() == kind::STORE) {
    AlwaysAssert(false, "Cannot use eager bitblasting on QF_ABV formula with stores");
  }
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    collectFunctionSymbols(term[i], seen);
  }
  seen.insert(term);
}

void TheoryBV::storeFunction(TNode func, TNode term) {
  if (d_funcToArgs.find(func) == d_funcToArgs.end()) {
    d_funcToArgs.insert(make_pair(func, NodeSet()));
  }
  NodeSet& set = d_funcToArgs[func];
  if (set.find(term) == set.end()) {
    set.insert(term);
    Node skolem = utils::mkVar(utils::getSize(term));
    d_funcToSkolem.addSubstitution(term, skolem);
  }
}

void TheoryBV::mkAckermanizationAsssertions(std::vector<Node>& assertions) {
  Debug("bv-ackermanize") << "TheoryBV::mkAckermanizationAsssertions\n";

  Assert(options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER);
  AlwaysAssert(!options::incrementalSolving());
  TNodeSet seen;
  for (unsigned i = 0; i < assertions.size(); ++i) {
    collectFunctionSymbols(assertions[i], seen);
  }

  FunctionToArgs::const_iterator it = d_funcToArgs.begin();
  NodeManager* nm = NodeManager::currentNM();
  for (; it!= d_funcToArgs.end(); ++it) {
    TNode func = it->first;
    const NodeSet& args = it->second;
    NodeSet::const_iterator it1 = args.begin();
    for ( ; it1 != args.end(); ++it1) {
      for(NodeSet::const_iterator it2 = it1; it2 != args.end(); ++it2) {
        TNode args1 = *it1;
        TNode args2 = *it2;
        Node args_eq;
        
        if (args1.getKind() == kind::APPLY_UF) {
          AlwaysAssert (args1.getKind() == kind::APPLY_UF &&
                        args1.getOperator() == func);
          AlwaysAssert (args2.getKind() == kind::APPLY_UF &&
                        args2.getOperator() == func);
          AlwaysAssert (args1.getNumChildren() == args2.getNumChildren());

          std::vector<Node> eqs(args1.getNumChildren());

          for (unsigned i = 0; i < args1.getNumChildren(); ++i) {
            eqs[i] = nm->mkNode(kind::EQUAL, args1[i], args2[i]);
          }
          args_eq = eqs.size() == 1 ? eqs[0] : nm->mkNode(kind::AND, eqs);
        } else {
          AlwaysAssert (args1.getKind() == kind::SELECT &&
                        args1[0] == func);
          AlwaysAssert (args2.getKind() == kind::SELECT &&
                        args2[0] == func);
          AlwaysAssert (args1.getNumChildren() == 2);
          AlwaysAssert (args2.getNumChildren() == 2);
          args_eq = nm->mkNode(kind::EQUAL, args1[1], args2[1]);
        }
        Node func_eq = nm->mkNode(kind::EQUAL, args1, args2);
        Node lemma = nm->mkNode(kind::IMPLIES, args_eq, func_eq);
        assertions.push_back(lemma);
      }
    }
  }

  // replace applications of UF by skolems (FIXME for model building)
  for(unsigned i = 0; i < assertions.size(); ++i) {
    assertions[i] = d_funcToSkolem.apply(assertions[i]);
  }
}

Node TheoryBV::expandDefinition(LogicRequest &logicRequest, Node node) {
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
    Node den_eq_0 = nm->mkNode(kind::EQUAL, den, nm->mkConst(BitVector(width, Integer(0))));
    Node divTotalNumDen = nm->mkNode(node.getKind() == kind::BITVECTOR_UDIV ? kind::BITVECTOR_UDIV_TOTAL :
				     kind::BITVECTOR_UREM_TOTAL, num, den);

    // if (options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER) {
    //   // Ackermanize UF if using eager bit-blasting
    //   Node ackerman_var = nm->mkNode(node.getKind() == kind::BITVECTOR_UDIV ? kind::BITVECTOR_ACKERMANIZE_UDIV : kind::BITVECTOR_ACKERMANIZE_UREM, num);
    //   node = nm->mkNode(kind::ITE, den_eq_0, ackerman_var, divTotalNumDen);
    //   return node;
    // } else {
      Node divByZero = getBVDivByZero(node.getKind(), width);
      Node divByZeroNum = nm->mkNode(kind::APPLY_UF, divByZero, num);
      node = nm->mkNode(kind::ITE, den_eq_0, divByZeroNum, divTotalNumDen);
      logicRequest.widenLogic(THEORY_UF);
      return node;
      //}
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

  if (options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER) {
    // the aig bit-blaster option is set heuristically
    // if bv abstraction is not used
    if (!d_eagerSolver->isInitialized()) {
      d_eagerSolver->initialize();
    }

    if (node.getKind() == kind::BITVECTOR_EAGER_ATOM) {
      Node formula = node[0];
      d_eagerSolver->assertFormula(formula);
    }
    // nothing to do for the other terms
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

void TheoryBV::checkForLemma(TNode fact) {
  if (fact.getKind() == kind::EQUAL) {
    if (fact[0].getKind() == kind::BITVECTOR_UREM_TOTAL) {
      TNode urem = fact[0];
      TNode result = fact[1];
      TNode divisor = urem[1];
      Node result_ult_div = mkNode(kind::BITVECTOR_ULT, result, divisor);
      Node divisor_eq_0 = mkNode(kind::EQUAL,
                                 divisor,
                                 mkConst(BitVector(getSize(divisor), 0u)));
      Node split = utils::mkNode(kind::OR, divisor_eq_0, mkNode(kind::NOT, fact), result_ult_div);
      lemma(split);
    }
    if (fact[1].getKind() == kind::BITVECTOR_UREM_TOTAL) {
      TNode urem = fact[1];
      TNode result = fact[0];
      TNode divisor = urem[1];
      Node result_ult_div = mkNode(kind::BITVECTOR_ULT, result, divisor);
      Node divisor_eq_0 = mkNode(kind::EQUAL,
                                 divisor,
                                 mkConst(BitVector(getSize(divisor), 0u)));
      Node split = utils::mkNode(kind::OR, divisor_eq_0, mkNode(kind::NOT, fact), result_ult_div);
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
  if( e==Theory::EFFORT_LAST_CALL ){
    std::vector< Node > nred;
    getExtTheory()->getActive( nred );
    doExtfReductions( nred );
    return;
  }

  TimerStat::CodeTimer checkTimer(d_checkTime);
  Debug("bitvector") << "TheoryBV::check(" << e << ")" << std::endl;
  TimerStat::CodeTimer codeTimer(d_statistics.d_solveTimer);
  // we may be getting new assertions so the model cache may not be sound
  d_invalidateModelCache.set(true);
  // if we are using the eager solver
  if (options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER) {
    // this can only happen on an empty benchmark
    if (!d_eagerSolver->isInitialized()) {
      d_eagerSolver->initialize();
    }
    if (!Theory::fullEffort(e))
      return;

    std::vector<TNode> assertions;
    while (!done()) {
      TNode fact = get().assertion;
      Assert (fact.getKind() == kind::BITVECTOR_EAGER_ATOM);
      assertions.push_back(fact);
    }
    Assert (d_eagerSolver->hasAssertions(assertions));

    bool ok = d_eagerSolver->checkSat();
    if (!ok) {
      if (assertions.size() == 1) {
        d_out->conflict(assertions[0]);
        return;
      }
      Node conflict = NodeManager::currentNM()->mkNode(kind::AND, assertions);
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
    TNode fact = get().assertion;

    checkForLemma(fact);

    for (unsigned i = 0; i < d_subtheories.size(); ++i) {
      d_subtheories[i]->assertFact(fact);
    }
  }

  bool ok = true;
  bool complete = false;
  for (unsigned i = 0; i < d_subtheories.size(); ++i) {
    Assert (!inConflict());
    ok = d_subtheories[i]->check(e);
    complete = d_subtheories[i]->isComplete();

    if (!ok) {
      // if we are in a conflict no need to check with other theories
      Assert (inConflict());
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

bool TheoryBV::doExtfInferences( std::vector< Node >& terms ) {
  bool sentLemma = false;
  eq::EqualityEngine * ee = getEqualityEngine();    
  std::map< Node, Node > op_map;
  for( unsigned j=0; j<terms.size(); j++ ){
    TNode n = terms[j];
    Assert( n.getKind()==kind::BITVECTOR_TO_NAT || kind::INT_TO_BITVECTOR );
    if( n.getKind()==kind::BITVECTOR_TO_NAT ){
      //range lemmas
      if( d_extf_range_infer.find( n )==d_extf_range_infer.end() ){
        d_extf_range_infer.insert( n );
        unsigned bvs = n[0].getType().getBitVectorSize();
        Node min = NodeManager::currentNM()->mkConst( Rational( 0 ) );
        Node max = NodeManager::currentNM()->mkConst( Rational( Integer(1).multiplyByPow2(bvs) ) );
        Node lem = NodeManager::currentNM()->mkNode( kind::AND, NodeManager::currentNM()->mkNode( kind::GEQ, n, min ), NodeManager::currentNM()->mkNode( kind::LT, n, max ) );
        Trace("bv-extf-lemma") << "BV extf lemma (range) : " << lem << std::endl;
        d_out->lemma( lem );
        sentLemma = true;
      }
    }
    Node r = ( ee && ee->hasTerm( n[0] ) ) ? ee->getRepresentative( n[0] ) : n[0];
    op_map[r] = n;
  }
  for( unsigned j=0; j<terms.size(); j++ ){
    TNode n = terms[j];
    Node r = ( ee && ee->hasTerm( n[0] ) ) ? ee->getRepresentative( n ) : n;
    std::map< Node, Node >::iterator it = op_map.find( r );
    if( it!=op_map.end() ){
      Node parent = it->second;
      //Node cterm = parent[0]==n ? parent : NodeManager::currentNM()->mkNode( parent.getOperator(), n );
      Node cterm = parent[0].eqNode( n );
      Trace("bv-extf-lemma-debug") << "BV extf collapse based on : " << cterm << std::endl;
      if( d_extf_collapse_infer.find( cterm )==d_extf_collapse_infer.end() ){
        d_extf_collapse_infer.insert( cterm );
      
        Node t = n[0];
        if( n.getKind()==kind::INT_TO_BITVECTOR ){
          Assert( t.getType().isInteger() );
          //congruent modulo 2^( bv width )
          unsigned bvs = n.getType().getBitVectorSize();
          Node coeff = NodeManager::currentNM()->mkConst( Rational( Integer(1).multiplyByPow2(bvs) ) );
          Node k = NodeManager::currentNM()->mkSkolem( "int_bv_cong", t.getType(), "for int2bv/bv2nat congruence" );
          t = NodeManager::currentNM()->mkNode( kind::PLUS, t, NodeManager::currentNM()->mkNode( kind::MULT, coeff, k ) );
        }
        Node lem = parent.eqNode( t );
        
        if( parent[0]!=n ){
          Assert( ee->areEqual( parent[0], n ) );
          lem = NodeManager::currentNM()->mkNode( kind::IMPLIES, parent[0].eqNode( n ), lem );
        }
        Trace("bv-extf-lemma") << "BV extf lemma (collapse) : " << lem << std::endl;
        d_out->lemma( lem );
        sentLemma = true;
      }
    }
  }
  return sentLemma;
}

bool TheoryBV::doExtfReductions( std::vector< Node >& terms ) {
  std::vector< Node > nredr;
  if( getExtTheory()->doReductions( 0, terms, nredr ) ){
    return true;
  }
  Assert( nredr.empty() );
  return false;
}

bool TheoryBV::needsCheckLastEffort() {
  return d_needsLastCallCheck;
}

void TheoryBV::collectModelInfo( TheoryModel* m, bool fullModel ){
  Assert(!inConflict());
  if (options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER) {
    d_eagerSolver->collectModelInfo(m, fullModel);
  }
  for (unsigned i = 0; i < d_subtheories.size(); ++i) {
    if (d_subtheories[i]->isComplete()) {
      d_subtheories[i]->collectModelInfo(m, fullModel);
      return;
    }
  }
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
  if (options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER) {
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

int TheoryBV::getReduction( int effort, Node n, Node& nr ) {
  Trace("bv-ext") << "TheoryBV::checkExt : non-reduced : " << n << std::endl;
  if( n.getKind()==kind::BITVECTOR_TO_NAT ){
    //taken from rewrite code
    const unsigned size = utils::getSize(n[0]);
    NodeManager* const nm = NodeManager::currentNM();
    const Node z = nm->mkConst(Rational(0));
    const Node bvone = nm->mkConst(BitVector(1u, 1u));
    NodeBuilder<> result(kind::PLUS);
    Integer i = 1;
    for(unsigned bit = 0; bit < size; ++bit, i *= 2) {
      Node cond = nm->mkNode(kind::EQUAL, nm->mkNode(nm->mkConst(BitVectorExtract(bit, bit)), n[0]), bvone);
      result << nm->mkNode(kind::ITE, cond, nm->mkConst(Rational(i)), z);
    }
    nr = Node(result);
    return -1;
  }else if( n.getKind()==kind::INT_TO_BITVECTOR ){
    //taken from rewrite code
    const unsigned size = n.getOperator().getConst<IntToBitVector>().size;
    NodeManager* const nm = NodeManager::currentNM();
    const Node bvzero = nm->mkConst(BitVector(1u, 0u));
    const Node bvone = nm->mkConst(BitVector(1u, 1u));
    std::vector<Node> v;
    Integer i = 2;
    while(v.size() < size) {
      Node cond = nm->mkNode(kind::GEQ, nm->mkNode(kind::INTS_MODULUS_TOTAL, n[0], nm->mkConst(Rational(i))), nm->mkConst(Rational(i, 2)));
      cond = Rewriter::rewrite( cond );
      v.push_back(nm->mkNode(kind::ITE, cond, bvone, bvzero));
      i *= 2;
    }
    NodeBuilder<> result(kind::BITVECTOR_CONCAT);
    result.append(v.rbegin(), v.rend());
    nr = Node(result);
    return -1;
  }
  return 0;
}
  
Theory::PPAssertStatus TheoryBV::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {
  switch(in.getKind()) {
  case kind::EQUAL:
    {
      if (in[0].isVar() && !in[1].hasSubterm(in[0])) {
        ++(d_statistics.d_solveSubstitutions);
        outSubstitutions.addSubstitution(in[0], in[1]);
        return PP_ASSERT_STATUS_SOLVED;
      }
      if (in[1].isVar() && !in[0].hasSubterm(in[1])) {
        ++(d_statistics.d_solveSubstitutions);
        outSubstitutions.addSubstitution(in[1], in[0]);
        return PP_ASSERT_STATUS_SOLVED;
      }
      Node node = Rewriter::rewrite(in);
      if ((node[0].getKind() == kind::BITVECTOR_EXTRACT && node[1].isConst()) ||
          (node[1].getKind() == kind::BITVECTOR_EXTRACT && node[0].isConst())) {
        Node extract = node[0].isConst() ? node[1] : node[0];
        if (extract[0].getKind() == kind::VARIABLE) {
          Node c = node[0].isConst() ? node[0] : node[1];

          unsigned high = utils::getExtractHigh(extract);
          unsigned low = utils::getExtractLow(extract);
          unsigned var_bitwidth = utils::getSize(extract[0]);
          std::vector<Node> children;

          if (low == 0) {
            Assert (high != var_bitwidth - 1);
            unsigned skolem_size = var_bitwidth - high - 1;
            Node skolem = utils::mkVar(skolem_size);
            children.push_back(skolem);
            children.push_back(c);
          } else if (high == var_bitwidth - 1) {
            unsigned skolem_size = low;
            Node skolem = utils::mkVar(skolem_size);
            children.push_back(c);
            children.push_back(skolem);
          } else {
            unsigned skolem1_size = low;
            unsigned skolem2_size = var_bitwidth - high - 1;
            Node skolem1 = utils::mkVar(skolem1_size);
            Node skolem2 = utils::mkVar(skolem2_size);
            children.push_back(skolem2);
            children.push_back(c);
            children.push_back(skolem1);
          }
          Node concat = utils::mkNode(kind::BITVECTOR_CONCAT, children);
          Assert (utils::getSize(concat) == utils::getSize(extract[0]));
          outSubstitutions.addSubstitution(extract[0], concat);
          return PP_ASSERT_STATUS_SOLVED;
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
  if (RewriteRule<BitwiseEq>::applies(t)) {
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
    Node new_eq =utils::mkNode(kind::EQUAL, sum, mult);
    Node rewr_eq = RewriteRule<SolveEq>::run<true>(new_eq);
    if (rewr_eq[0].isVar() || rewr_eq[1].isVar()){
      res = Rewriter::rewrite(rewr_eq);
    } else {
      res = t;
    }
  }


  // if(t.getKind() == kind::EQUAL &&
  //    ((t[0].getKind() == kind::BITVECTOR_MULT && t[1].getKind() == kind::BITVECTOR_PLUS) ||
  //     (t[1].getKind() == kind::BITVECTOR_MULT && t[0].getKind() == kind::BITVECTOR_PLUS))) {
  //   // if we have an equality between a multiplication and addition
  //   // try to express multiplication in terms of addition
  //   Node mult = t[0].getKind() == kind::BITVECTOR_MULT? t[0] : t[1];
  //   Node add = t[0].getKind() == kind::BITVECTOR_PLUS? t[0] : t[1];
  //   if (RewriteRule<MultSlice>::applies(mult)) {
  //     Node new_mult = RewriteRule<MultSlice>::run<false>(mult);
  //     Node new_eq = Rewriter::rewrite(utils::mkNode(kind::EQUAL, new_mult, add));

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
  // * bitblaster needs to be left alone until it's done, otherwise it doesn't know how to explain
  // * equality engine can propagate eagerly
  bool ok = true;
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
  Assert (wasPropagatedBySubtheory(literal));
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
  if (options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER)
    return EQUALITY_UNKNOWN;
  Assert (options::bitblastMode() == theory::bv::BITBLAST_MODE_LAZY);
  for (unsigned i = 0; i < d_subtheories.size(); ++i) {
    EqualityStatus status = d_subtheories[i]->getEqualityStatus(a, b);
    if (status != EQUALITY_UNKNOWN) {
      return status;
    }
  }
  return EQUALITY_UNKNOWN; ;
}


void TheoryBV::enableCoreTheorySlicer() {
  Assert (!d_calledPreregister);
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

          Node dis = utils::mkNode(kind::OR, b_eq_0, c_eq_0, b_eq_c);
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
  if (changed &&
      options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER &&
      options::bitvectorAig()) {
    // disable AIG mode
    AlwaysAssert (!d_eagerSolver->isInitialized());
    d_eagerSolver->turnOffAig();
    d_eagerSolver->initialize();
  }
  return changed;
}

void TheoryBV::setProofLog( BitVectorProof * bvp ) {
  if( options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER ){
    d_eagerSolver->setProofLog( bvp );
  }else{
    for( unsigned i=0; i< d_subtheories.size(); i++ ){
      d_subtheories[i]->setProofLog( bvp );
    }
  }
}

void TheoryBV::setConflict(Node conflict) {
  if (options::bvAbstraction()) {
    Node new_conflict = d_abstractionModule->simplifyConflict(conflict);

    std::vector<Node> lemmas;
    lemmas.push_back(new_conflict);
    d_abstractionModule->generalizeConflict(new_conflict, lemmas);
    for (unsigned i = 0; i < lemmas.size(); ++i) {
      lemma(utils::mkNode(kind::NOT, lemmas[i]));
    }
  }
  d_conflict = true;
  d_conflictNode = conflict;
}

} /* namespace CVC4::theory::bv */
} /* namespace CVC4::theory */
} /* namespace CVC4 */
