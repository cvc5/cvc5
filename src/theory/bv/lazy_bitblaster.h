/*********************                                                        */
/*! \file lazy_bitblaster.h
** \verbatim
** Original author: Liana Hadarean
** Major contributors: none
** Minor contributors (to current version): lianah
** This file is part of the CVC4 project.
** Copyright (c) 2009-2013  New York University and The University of Iowa
** See the file COPYING in the top-level source directory for licensing
** information.\endverbatim
**
** \brief 
**
** Bitblaster for the lazy bv solver. 
**/

#include "cvc4_private.h"

#ifndef __CVC4__LAZY__BITBLASTER_H
#define __CVC4__LAZY__BITBLASTER_H


#include "bitblaster_template.h"
#include "theory_bv_utils.h"
#include "theory/rewriter.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_factory.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/options.h"
#include "theory/theory_model.h"
#include "theory/bv/abstraction.h"

namespace CVC4 {
namespace theory {
namespace bv {

TLazyBitblaster::TLazyBitblaster(context::Context* c, bv::TheoryBV* bv, const std::string name, bool emptyNotify)
  : TBitblaster<Node>()
  , d_bv(bv)
  , d_ctx(c)
  , d_assertedAtoms(new(true) context::CDList<prop::SatLiteral>(c))
  , d_explanations(new(true) ExplanationMap(c))
  , d_variables()
  , d_bbAtoms()
  , d_abstraction(NULL)
  , d_emptyNotify(emptyNotify)
  , d_name(name)
  , d_statistics(name) {
  d_satSolver = prop::SatSolverFactory::createMinisat(c, name);
  d_nullRegistrar = new prop::NullRegistrar();
  d_nullContext = new context::Context();
  d_cnfStream = new prop::TseitinCnfStream(d_satSolver,
                                           d_nullRegistrar,
                                           d_nullContext);
  
  prop::BVSatSolverInterface::Notify* notify = d_emptyNotify ?
    (prop::BVSatSolverInterface::Notify*) new MinisatEmptyNotify() :
    (prop::BVSatSolverInterface::Notify*) new MinisatNotify(d_cnfStream, bv, this);

  d_satSolver->setNotify(notify);
}

void TLazyBitblaster::setAbstraction(AbstractionModule* abs) {
  d_abstraction = abs; 
}

TLazyBitblaster::~TLazyBitblaster() {
  delete d_cnfStream;
  delete d_nullRegistrar;
  delete d_nullContext;
  delete d_satSolver;
}


/**
 * Bitblasts the atom, assigns it a marker literal, adding it to the SAT solver
 * NOTE: duplicate clauses are not detected because of marker literal
 * @param node the atom to be bitblasted
 *
 */
void TLazyBitblaster::bbAtom(TNode node) {
  node = node.getKind() == kind::NOT?  node[0] : node;

  if (hasBBAtom(node)) {
    return;
  }

  // make sure it is marked as an atom
  addAtom(node);

  Debug("bitvector-bitblast") << "Bitblasting node " << node <<"\n";
  ++d_statistics.d_numAtoms;

  /// if we are using bit-vector abstraction bit-blast the original interpretation
  if (options::bvAbstraction() &&
      d_abstraction != NULL &&
      d_abstraction->isAbstraction(node)) {
    // node must be of the form P(args) = bv1
    Node expansion = Rewriter::rewrite(d_abstraction->getInterpretation(node));

    Node atom_bb;
    if (expansion.getKind() == kind::CONST_BOOLEAN) {
      atom_bb = expansion;
    } else {
      Assert (expansion.getKind() == kind::AND); 
      std::vector<Node> atoms; 
      for (unsigned i = 0; i < expansion.getNumChildren(); ++i) {
        Node normalized_i = Rewriter::rewrite(expansion[i]);
        Node atom_i = normalized_i.getKind() != kind::CONST_BOOLEAN ?
          Rewriter::rewrite(d_atomBBStrategies[normalized_i.getKind()](normalized_i, this)) :
          normalized_i;
        atoms.push_back(atom_i);
      }
      atom_bb = utils::mkAnd(atoms);
    }
    Assert (!atom_bb.isNull()); 
    Node atom_definition = utils::mkNode(kind::IFF, node, atom_bb);
    storeBBAtom(node, atom_bb);
    d_cnfStream->convertAndAssert(atom_definition, false, false); 
    return; 
  }

  // the bitblasted definition of the atom
  Node normalized = Rewriter::rewrite(node);
  Node atom_bb = normalized.getKind() != kind::CONST_BOOLEAN ?
    Rewriter::rewrite(d_atomBBStrategies[normalized.getKind()](normalized, this)) :
    normalized;
  // asserting that the atom is true iff the definition holds
  Node atom_definition = utils::mkNode(kind::IFF, node, atom_bb);
  storeBBAtom(node, atom_bb);
  d_cnfStream->convertAndAssert(atom_definition, false, false);
}

void TLazyBitblaster::storeBBAtom(TNode atom, Node atom_bb) {
  // no need to store the definition for the lazy bit-blaster
  d_bbAtoms.insert(atom); 
}

bool TLazyBitblaster::hasBBAtom(TNode atom) const {
  return d_bbAtoms.find(atom) != d_bbAtoms.end(); 
}


void TLazyBitblaster::makeVariable(TNode var, Bits& bits) {
  Assert(bits.size() == 0);
  for (unsigned i = 0; i < utils::getSize(var); ++i) {
    bits.push_back(utils::mkBitOf(var, i)); 
  }
  d_variables.insert(var); 
}

uint64_t TLazyBitblaster::computeAtomWeight(TNode node, NodeSet& seen) {
  node = node.getKind() == kind::NOT?  node[0] : node;

  Node atom_bb = Rewriter::rewrite(d_atomBBStrategies[node.getKind()](node, this));
  uint64_t size = utils::numNodes(atom_bb, seen);
  return size;
}

// cnf conversion ensures the atom represents itself
Node TLazyBitblaster::getBBAtom(TNode node) const {
  return node; 
}

void TLazyBitblaster::bbTerm(TNode node, Bits& bits) {

  if (hasBBTerm(node)) {
    getBBTerm(node, bits);
    return;
  }

  Debug("bitvector-bitblast") << "Bitblasting node " << node <<"\n";
  ++d_statistics.d_numTerms;

  d_termBBStrategies[node.getKind()] (node, bits,this);

  Assert (bits.size() == utils::getSize(node));

  storeBBTerm(node, bits);
}
/// Public methods

void TLazyBitblaster::addAtom(TNode atom) {
  d_cnfStream->ensureLiteral(atom);
  prop::SatLiteral lit = d_cnfStream->getLiteral(atom);
  d_satSolver->addMarkerLiteral(lit);
}

void TLazyBitblaster::explain(TNode atom, std::vector<TNode>& explanation) {
  prop::SatLiteral lit = d_cnfStream->getLiteral(atom);

  ++(d_statistics.d_numExplainedPropagations);
  if (options::bvEagerExplanations()) {
    Assert (d_explanations->find(lit) != d_explanations->end());
    const std::vector<prop::SatLiteral>& literal_explanation = (*d_explanations)[lit].get();
    for (unsigned i = 0; i < literal_explanation.size(); ++i) {
      explanation.push_back(d_cnfStream->getNode(literal_explanation[i]));
    }
    return; 
  }
  
  std::vector<prop::SatLiteral> literal_explanation;
  d_satSolver->explain(lit, literal_explanation);
  for (unsigned i = 0; i < literal_explanation.size(); ++i) {
    explanation.push_back(d_cnfStream->getNode(literal_explanation[i]));
  }
}


/*
 * Asserts the clauses corresponding to the atom to the Sat Solver
 * by turning on the marker literal (i.e. setting it to false)
 * @param node the atom to be asserted
 *
 */

bool TLazyBitblaster::propagate() {
  return d_satSolver->propagate() == prop::SAT_VALUE_TRUE;
}

bool TLazyBitblaster::assertToSat(TNode lit, bool propagate) {
  // strip the not
  TNode atom;
  if (lit.getKind() == kind::NOT) {
    atom = lit[0];
  } else {
    atom = lit;
  }

  Assert (hasBBAtom(atom));

  prop::SatLiteral markerLit = d_cnfStream->getLiteral(atom);

  if(lit.getKind() == kind::NOT) {
    markerLit = ~markerLit;
  }

  Debug("bitvector-bb") << "TheoryBV::TLazyBitblaster::assertToSat asserting node: " << atom <<"\n";
  Debug("bitvector-bb") << "TheoryBV::TLazyBitblaster::assertToSat with literal:   " << markerLit << "\n";

  prop::SatValue ret = d_satSolver->assertAssumption(markerLit, propagate);

  d_assertedAtoms->push_back(markerLit);

  return ret == prop::SAT_VALUE_TRUE || ret == prop::SAT_VALUE_UNKNOWN;
}

/**
 * Calls the solve method for the Sat Solver.
 * passing it the marker literals to be asserted
 *
 * @return true for sat, and false for unsat
 */

bool TLazyBitblaster::solve() {
  if (Trace.isOn("bitvector")) {
    Trace("bitvector") << "TLazyBitblaster::solve() asserted atoms ";
    context::CDList<prop::SatLiteral>::const_iterator it = d_assertedAtoms->begin();
    for (; it != d_assertedAtoms->end(); ++it) {
      Trace("bitvector") << "     " << d_cnfStream->getNode(*it) << "\n";
    }
  }
  Debug("bitvector") << "TLazyBitblaster::solve() asserted atoms " << d_assertedAtoms->size() <<"\n";
  return prop::SAT_VALUE_TRUE == d_satSolver->solve();
}

prop::SatValue TLazyBitblaster::solveWithBudget(unsigned long budget) {
  if (Trace.isOn("bitvector")) {
    Trace("bitvector") << "TLazyBitblaster::solveWithBudget() asserted atoms ";
    context::CDList<prop::SatLiteral>::const_iterator it = d_assertedAtoms->begin();
    for (; it != d_assertedAtoms->end(); ++it) {
      Trace("bitvector") << "     " << d_cnfStream->getNode(*it) << "\n";
    }
  }
  Debug("bitvector") << "TLazyBitblaster::solveWithBudget() asserted atoms " << d_assertedAtoms->size() <<"\n";
  return d_satSolver->solve(budget);
}


void TLazyBitblaster::getConflict(std::vector<TNode>& conflict) {
  prop::SatClause conflictClause;
  d_satSolver->getUnsatCore(conflictClause);

  for (unsigned i = 0; i < conflictClause.size(); i++) {
    prop::SatLiteral lit = conflictClause[i];
    TNode atom = d_cnfStream->getNode(lit);
    Node  not_atom;
    if (atom.getKind() == kind::NOT) {
      not_atom = atom[0];
    } else {
      not_atom = NodeManager::currentNM()->mkNode(kind::NOT, atom);
    }
    conflict.push_back(not_atom);
  }
}

TLazyBitblaster::Statistics::Statistics(const std::string& prefix) :
  d_numTermClauses("theory::bv::"+prefix+"::NumberOfTermSatClauses", 0),
  d_numAtomClauses("theory::bv::"+prefix+"::NumberOfAtomSatClauses", 0),
  d_numTerms("theory::bv::"+prefix+"::NumberOfBitblastedTerms", 0),
  d_numAtoms("theory::bv::"+prefix+"::NumberOfBitblastedAtoms", 0),
  d_numExplainedPropagations("theory::bv::"+prefix+"::NumberOfExplainedPropagations", 0),
  d_numBitblastingPropagations("theory::bv::"+prefix+"::NumberOfBitblastingPropagations", 0),
  d_bitblastTimer("theory::bv::"+prefix+"::BitblastTimer")
{
  StatisticsRegistry::registerStat(&d_numTermClauses);
  StatisticsRegistry::registerStat(&d_numAtomClauses);
  StatisticsRegistry::registerStat(&d_numTerms);
  StatisticsRegistry::registerStat(&d_numAtoms);
  StatisticsRegistry::registerStat(&d_numExplainedPropagations);
  StatisticsRegistry::registerStat(&d_numBitblastingPropagations);
  StatisticsRegistry::registerStat(&d_bitblastTimer);
}


TLazyBitblaster::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_numTermClauses);
  StatisticsRegistry::unregisterStat(&d_numAtomClauses);
  StatisticsRegistry::unregisterStat(&d_numTerms);
  StatisticsRegistry::unregisterStat(&d_numAtoms);
  StatisticsRegistry::unregisterStat(&d_numExplainedPropagations);
  StatisticsRegistry::unregisterStat(&d_numBitblastingPropagations);
  StatisticsRegistry::unregisterStat(&d_bitblastTimer);
}

bool TLazyBitblaster::MinisatNotify::notify(prop::SatLiteral lit) {
  if(options::bvEagerExplanations()) {
    // compute explanation
    if (d_lazyBB->d_explanations->find(lit) == d_lazyBB->d_explanations->end()) {
      std::vector<prop::SatLiteral> literal_explanation;
      d_lazyBB->d_satSolver->explain(lit, literal_explanation);
      d_lazyBB->d_explanations->insert(lit, literal_explanation);
    } else {
      // we propagated it at a lower level
      return true; 
    }
  }
  ++(d_lazyBB->d_statistics.d_numBitblastingPropagations);
  TNode atom = d_cnf->getNode(lit); 
  return d_bv->storePropagation(atom, SUB_BITBLAST);
}

void TLazyBitblaster::MinisatNotify::notify(prop::SatClause& clause) {
  if (clause.size() > 1) {
    NodeBuilder<> lemmab(kind::OR);
    for (unsigned i = 0; i < clause.size(); ++ i) {
      lemmab << d_cnf->getNode(clause[i]);
    }
    Node lemma = lemmab;
    d_bv->d_out->lemma(lemma);
  } else {
    d_bv->d_out->lemma(d_cnf->getNode(clause[0]));
  }
}

void TLazyBitblaster::MinisatNotify::safePoint() {
  d_bv->d_out->safePoint();
}

EqualityStatus TLazyBitblaster::getEqualityStatus(TNode a, TNode b) {

  // We don't want to bit-blast every possibly expensive term for the sake of equality checking
  if (hasBBTerm(a) && hasBBTerm(b)) {

    Bits a_bits, b_bits;
    getBBTerm(a, a_bits);
    getBBTerm(b, b_bits);
    theory::EqualityStatus status = theory::EQUALITY_TRUE_IN_MODEL;
    for (unsigned i = 0; i < a_bits.size(); ++ i) {
      if (d_cnfStream->hasLiteral(a_bits[i]) && d_cnfStream->hasLiteral(b_bits[i])) {
        prop::SatLiteral a_lit = d_cnfStream->getLiteral(a_bits[i]);
        prop::SatValue a_lit_value = d_satSolver->value(a_lit);
        if (a_lit_value != prop::SAT_VALUE_UNKNOWN) {
          prop::SatLiteral b_lit = d_cnfStream->getLiteral(b_bits[i]);
          prop::SatValue b_lit_value = d_satSolver->value(b_lit);
          if (b_lit_value != prop::SAT_VALUE_UNKNOWN) {
            if (a_lit_value != b_lit_value) {
              return theory::EQUALITY_FALSE_IN_MODEL;
            }
          } else {
            status = theory::EQUALITY_UNKNOWN;
          }
        } {
          status = theory::EQUALITY_UNKNOWN;
        }
      } else {
        status = theory::EQUALITY_UNKNOWN;
      }
    }

    return status;

  } else {
    return theory::EQUALITY_UNKNOWN;
  }
}


bool TLazyBitblaster::isSharedTerm(TNode node) {
  return d_bv->d_sharedTermsSet.find(node) != d_bv->d_sharedTermsSet.end();
}

bool TLazyBitblaster::hasValue(TNode a) {
  Assert (hasBBTerm(a)); 
  Bits bits;
  getBBTerm(a, bits); 
  for (int i = bits.size() -1; i >= 0; --i) {
    prop::SatValue bit_value;
    if (d_cnfStream->hasLiteral(bits[i])) {
      prop::SatLiteral bit = d_cnfStream->getLiteral(bits[i]);
      bit_value = d_satSolver->value(bit);
      if (bit_value ==  prop::SAT_VALUE_UNKNOWN)
        return false;
    } else {
      return false;
    }
  }
  return true;
}
/**
 * Returns the value a is currently assigned to in the SAT solver
 * or null if the value is completely unassigned.
 *
 * @param a
 * @param fullModel whether to create a "full model," i.e., add
 * constants to equivalence classes that don't already have them
 *
 * @return
 */
Node TLazyBitblaster::getVarValue(TNode a, bool fullModel) {
  if (!hasBBTerm(a)) {
    Assert(isSharedTerm(a));
    return Node();
  }
  Bits bits;
  getBBTerm(a, bits);
  Integer value(0);
  for (int i = bits.size() -1; i >= 0; --i) {
    prop::SatValue bit_value;
    if (d_cnfStream->hasLiteral(bits[i])) {
      prop::SatLiteral bit = d_cnfStream->getLiteral(bits[i]);
      bit_value = d_satSolver->value(bit);
      Assert (bit_value != prop::SAT_VALUE_UNKNOWN);
    } else {
      // the bit is unconstrainted so we can give it an arbitrary value
      bit_value = prop::SAT_VALUE_FALSE;
    }
    Integer bit_int = bit_value == prop::SAT_VALUE_TRUE ? Integer(1) : Integer(0);
    value = value * 2 + bit_int;
  }
  return utils::mkConst(BitVector(bits.size(), value));
}

void TLazyBitblaster::collectModelInfo(TheoryModel* m, bool fullModel) {
  TNodeSet::iterator it = d_variables.begin();
  for (; it!= d_variables.end(); ++it) {
    TNode var = *it;
    if (Theory::theoryOf(var) == theory::THEORY_BV || isSharedTerm(var))  {
      Node const_value = getVarValue(var, fullModel);
      if(const_value == Node()) {
        if( fullModel ){
          // if the value is unassigned just set it to zero
          const_value = utils::mkConst(BitVector(utils::getSize(var), 0u));
        }
      }
      if(const_value != Node()) {
        Debug("bitvector-model") << "TLazyBitblaster::collectModelInfo (assert (= "
                                 << var << " "
                                 << const_value << "))\n";
        m->assertEquality(var, const_value, true);
      }
    }
  }
}

void TLazyBitblaster::clearSolver() {
  Assert (d_ctx->getLevel() == 0); 
  delete d_satSolver;
  delete d_cnfStream;
  d_assertedAtoms->deleteSelf();
  d_assertedAtoms = new(true) context::CDList<prop::SatLiteral>(d_ctx);
  d_explanations->deleteSelf();
  d_explanations = new(true) ExplanationMap(d_ctx);
  d_bbAtoms.clear();
  d_variables.clear();
  d_termCache.clear(); 

  // recreate sat solver
  d_satSolver = prop::SatSolverFactory::createMinisat(d_ctx);
  d_cnfStream = new prop::TseitinCnfStream(d_satSolver,
                                           new prop::NullRegistrar(),
                                           new context::Context());

  prop::BVSatSolverInterface::Notify* notify = d_emptyNotify ?
    (prop::BVSatSolverInterface::Notify*) new MinisatEmptyNotify() :
    (prop::BVSatSolverInterface::Notify*) new MinisatNotify(d_cnfStream, d_bv, this);
  d_satSolver->setNotify(notify);
}

} /*bv namespace */
} /* theory namespace */
} /* CVC4 namespace*/

#endif
