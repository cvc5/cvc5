/*********************                                                        */
/*! \file bitblaster.cpp
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Dejan Jovanovic
 ** Minor contributors (to current version): Clark Barrett, Morgan Deters, lianah
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** 
 **/

#include "bitblaster.h"
#include "theory_bv_utils.h"
#include "theory/rewriter.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_factory.h"
#include "theory/bv/theory_bv_rewrite_rules_simplification.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/options.h"
#include "theory/model.h"

using namespace std;

using namespace CVC4::theory::bv::utils;
using namespace CVC4::context; 
using namespace CVC4::prop;

namespace CVC4 {
namespace theory {
namespace bv{

std::string toString(Bits&  bits) {
  ostringstream os; 
  for (int i = bits.size() - 1; i >= 0; --i) {
    TNode bit = bits[i];
    if (bit.getKind() == kind::CONST_BOOLEAN) {
      os << (bit.getConst<bool>() ? "1" : "0");
    } else {
      os << bit<< " ";   
    }
  }
  os <<"\n";
  
  return os.str(); 
}
/////// Bitblaster 

Bitblaster::Bitblaster(context::Context* c, bv::TheoryBV* bv) :
    d_bv(bv),
    d_bvOutput(bv->d_out),
    d_termCache(),
    d_bitblastedAtoms(),
    d_assertedAtoms(c),
    d_statistics()
  {
    d_satSolver = prop::SatSolverFactory::createMinisat(c);
    d_cnfStream = new TseitinCnfStream(d_satSolver, new NullRegistrar(), new Context());

    MinisatNotify* notify = new MinisatNotify(d_cnfStream, bv);
    d_satSolver->setNotify(notify); 
    // initializing the bit-blasting strategies
    initAtomBBStrategies(); 
    initTermBBStrategies(); 
  }

Bitblaster::~Bitblaster() {
  delete d_cnfStream;
  delete d_satSolver; 
}


/** 
 * Bitblasts the atom, assigns it a marker literal, adding it to the SAT solver
 * NOTE: duplicate clauses are not detected because of marker literal
 * @param node the atom to be bitblasted
 * 
 */
void Bitblaster::bbAtom(TNode node) {
  node = node.getKind() == kind::NOT?  node[0] : node;
  
  if (hasBBAtom(node)) {
    return; 
  }

  // make sure it is marked as an atom
  addAtom(node); 

  Debug("bitvector-bitblast") << "Bitblasting node " << node <<"\n"; 
  ++d_statistics.d_numAtoms;
  // the bitblasted definition of the atom
  Node atom_bb = Rewriter::rewrite(d_atomBBStrategies[node.getKind()](node, this));
  // asserting that the atom is true iff the definition holds
  Node atom_definition = mkNode(kind::IFF, node, atom_bb);

  if (!options::bitvectorEagerBitblast()) {
    d_cnfStream->convertAndAssert(atom_definition, false, false);
    d_bitblastedAtoms.insert(node);
  } else {
    d_bvOutput->lemma(atom_definition, false);
    d_bitblastedAtoms.insert(node);
  }
}

uint64_t Bitblaster::computeAtomWeight(TNode node) {
  node = node.getKind() == kind::NOT?  node[0] : node;

  Node atom_bb = Rewriter::rewrite(d_atomBBStrategies[node.getKind()](node, this));
  uint64_t size = utils::numNodes(atom_bb);
  return size;
}

void Bitblaster::bbTerm(TNode node, Bits& bits) {

  if (hasBBTerm(node)) {
    getBBTerm(node, bits);
    return;
  }

  Debug("bitvector-bitblast") << "Bitblasting node " << node <<"\n"; 
  ++d_statistics.d_numTerms;

  d_termBBStrategies[node.getKind()] (node, bits,this);
  
  Assert (bits.size() == utils::getSize(node));

  cacheTermDef(node, bits); 
}

Node Bitblaster::bbOptimize(TNode node) {
  std::vector<Node> children;

   if (node.getKind() == kind::BITVECTOR_PLUS) {
    if (RewriteRule<BBPlusNeg>::applies(node)) {
      Node res = RewriteRule<BBPlusNeg>::run<false>(node);
      return res; 
    }
    //  if (RewriteRule<BBFactorOut>::applies(node)) {
    //   Node res = RewriteRule<BBFactorOut>::run<false>(node);
    //   return res; 
    // } 

  } else if (node.getKind() == kind::BITVECTOR_MULT) {
    if (RewriteRule<MultPow2>::applies(node)) {
      Node res = RewriteRule<MultPow2>::run<false>(node);
      return res; 
    }
  }
  
  return node; 
}

/// Public methods

void Bitblaster::addAtom(TNode atom) {
  if (!options::bitvectorEagerBitblast()) {
    d_cnfStream->ensureLiteral(atom);
    SatLiteral lit = d_cnfStream->getLiteral(atom);
    d_satSolver->addMarkerLiteral(lit);
  }
}

void Bitblaster::explain(TNode atom, std::vector<TNode>& explanation) {
  std::vector<SatLiteral> literal_explanation;
  d_satSolver->explain(d_cnfStream->getLiteral(atom), literal_explanation);
  for (unsigned i = 0; i < literal_explanation.size(); ++i) {
    explanation.push_back(d_cnfStream->getNode(literal_explanation[i])); 
  }
}


/** 
 * Asserts the clauses corresponding to the atom to the Sat Solver
 * by turning on the marker literal (i.e. setting it to false)
 * @param node the atom to be asserted
 * 
 */
 
bool Bitblaster::propagate() {
  return d_satSolver->propagate() == prop::SAT_VALUE_TRUE;
}

bool Bitblaster::assertToSat(TNode lit, bool propagate) {
  // strip the not
  TNode atom; 
  if (lit.getKind() == kind::NOT) {
    atom = lit[0]; 
  } else {
    atom = lit; 
  }
  
  Assert (hasBBAtom(atom));

  SatLiteral markerLit = d_cnfStream->getLiteral(atom);

  if(lit.getKind() == kind::NOT) {
    markerLit = ~markerLit;
  }
  
  Debug("bitvector-bb") << "TheoryBV::Bitblaster::assertToSat asserting node: " << atom <<"\n";
  Debug("bitvector-bb") << "TheoryBV::Bitblaster::assertToSat with literal:   " << markerLit << "\n";  

  SatValue ret = d_satSolver->assertAssumption(markerLit, propagate);

  d_assertedAtoms.push_back(markerLit);

  Assert(ret != prop::SAT_VALUE_UNKNOWN);
  return ret == prop::SAT_VALUE_TRUE;
}

/** 
 * Calls the solve method for the Sat Solver. 
 * passing it the marker literals to be asserted
 * 
 * @return true for sat, and false for unsat
 */
 
bool Bitblaster::solve(bool quick_solve) {
  if (Trace.isOn("bitvector")) {
    Trace("bitvector") << "Bitblaster::solve() asserted atoms ";
    context::CDList<prop::SatLiteral>::const_iterator it = d_assertedAtoms.begin();
    for (; it != d_assertedAtoms.end(); ++it) {
      Trace("bitvector") << "     " << d_cnfStream->getNode(*it) << "\n";
    }
  }
  Debug("bitvector") << "Bitblaster::solve() asserted atoms " << d_assertedAtoms.size() <<"\n"; 
  return SAT_VALUE_TRUE == d_satSolver->solve(); 
}

void Bitblaster::getConflict(std::vector<TNode>& conflict) {
  SatClause conflictClause;
  d_satSolver->getUnsatCore(conflictClause);
  
  for (unsigned i = 0; i < conflictClause.size(); i++) {
    SatLiteral lit = conflictClause[i]; 
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


/// Helper methods


void Bitblaster::initAtomBBStrategies() {
  for (int i = 0 ; i < kind::LAST_KIND; ++i ) {
    d_atomBBStrategies[i] = UndefinedAtomBBStrategy; 
  }
  
  /// setting default bb strategies for atoms
  d_atomBBStrategies [ kind::EQUAL ]           = DefaultEqBB;
  d_atomBBStrategies [ kind::BITVECTOR_ULT ]   = DefaultUltBB;
  d_atomBBStrategies [ kind::BITVECTOR_ULE ]   = DefaultUleBB;
  d_atomBBStrategies [ kind::BITVECTOR_UGT ]   = DefaultUgtBB;
  d_atomBBStrategies [ kind::BITVECTOR_UGE ]   = DefaultUgeBB;
  d_atomBBStrategies [ kind::BITVECTOR_SLT ]   = DefaultSltBB;
  d_atomBBStrategies [ kind::BITVECTOR_SLE ]   = DefaultSleBB;
  d_atomBBStrategies [ kind::BITVECTOR_SGT ]   = DefaultSgtBB;
  d_atomBBStrategies [ kind::BITVECTOR_SGE ]   = DefaultSgeBB;
  
}

void Bitblaster::initTermBBStrategies() {
  // Changed this to DefaultVarBB because any foreign kind should be treated as a variable
  // TODO: check this is OK
  for (int i = 0 ; i < kind::LAST_KIND; ++i ) {
    d_termBBStrategies[i] = DefaultVarBB;
  }
  
  /// setting default bb strategies for terms:
  //  d_termBBStrategies [ kind::VARIABLE ]               = DefaultVarBB;
  d_termBBStrategies [ kind::CONST_BITVECTOR ]        = DefaultConstBB;
  d_termBBStrategies [ kind::BITVECTOR_NOT ]          = DefaultNotBB;
  d_termBBStrategies [ kind::BITVECTOR_CONCAT ]       = DefaultConcatBB;
  d_termBBStrategies [ kind::BITVECTOR_AND ]          = DefaultAndBB;
  d_termBBStrategies [ kind::BITVECTOR_OR ]           = DefaultOrBB;
  d_termBBStrategies [ kind::BITVECTOR_XOR ]          = DefaultXorBB;
  d_termBBStrategies [ kind::BITVECTOR_XNOR ]         = DefaultXnorBB;
  d_termBBStrategies [ kind::BITVECTOR_NAND ]         = DefaultNandBB ;
  d_termBBStrategies [ kind::BITVECTOR_NOR ]          = DefaultNorBB;
  d_termBBStrategies [ kind::BITVECTOR_COMP ]         = DefaultCompBB ;
  d_termBBStrategies [ kind::BITVECTOR_MULT ]         = DefaultMultBB;
  d_termBBStrategies [ kind::BITVECTOR_PLUS ]         = DefaultPlusBB;
  d_termBBStrategies [ kind::BITVECTOR_SUB ]          = DefaultSubBB;
  d_termBBStrategies [ kind::BITVECTOR_NEG ]          = DefaultNegBB;
  d_termBBStrategies [ kind::BITVECTOR_UDIV ]         = UndefinedTermBBStrategy; 
  d_termBBStrategies [ kind::BITVECTOR_UREM ]         = UndefinedTermBBStrategy; 
  d_termBBStrategies [ kind::BITVECTOR_UDIV_TOTAL ]   = DefaultUdivBB;
  d_termBBStrategies [ kind::BITVECTOR_UREM_TOTAL ]   = DefaultUremBB;
  d_termBBStrategies [ kind::BITVECTOR_SDIV ]         = UndefinedTermBBStrategy; 
  d_termBBStrategies [ kind::BITVECTOR_SREM ]         = UndefinedTermBBStrategy; 
  d_termBBStrategies [ kind::BITVECTOR_SMOD ]         = UndefinedTermBBStrategy; 
  d_termBBStrategies [ kind::BITVECTOR_SHL ]          = DefaultShlBB;
  d_termBBStrategies [ kind::BITVECTOR_LSHR ]         = DefaultLshrBB;
  d_termBBStrategies [ kind::BITVECTOR_ASHR ]         = DefaultAshrBB;
  d_termBBStrategies [ kind::BITVECTOR_EXTRACT ]      = DefaultExtractBB;
  d_termBBStrategies [ kind::BITVECTOR_REPEAT ]       = DefaultRepeatBB;
  d_termBBStrategies [ kind::BITVECTOR_ZERO_EXTEND ]  = DefaultZeroExtendBB;
  d_termBBStrategies [ kind::BITVECTOR_SIGN_EXTEND ]  = DefaultSignExtendBB;
  d_termBBStrategies [ kind::BITVECTOR_ROTATE_RIGHT ] = DefaultRotateRightBB;
  d_termBBStrategies [ kind::BITVECTOR_ROTATE_LEFT ]  = DefaultRotateLeftBB;

}
 
bool Bitblaster::hasBBAtom(TNode atom) const {
  return d_bitblastedAtoms.find(atom) != d_bitblastedAtoms.end();
}

void Bitblaster::cacheTermDef(TNode term, Bits def) {
  Assert (d_termCache.find(term) == d_termCache.end());
  d_termCache[term] = def; 
}

bool Bitblaster::hasBBTerm(TNode node) const {
  return d_termCache.find(node) != d_termCache.end(); 
}

void Bitblaster::getBBTerm(TNode node, Bits& bits) const {
  Assert (hasBBTerm(node)); 
  // copy?
  bits = d_termCache.find(node)->second;
}

Bitblaster::Statistics::Statistics() :
  d_numTermClauses("theory::bv::NumberOfTermSatClauses", 0),
  d_numAtomClauses("theory::bv::NumberOfAtomSatClauses", 0),
  d_numTerms("theory::bv::NumberOfBitblastedTerms", 0),
  d_numAtoms("theory::bv::NumberOfBitblastedAtoms", 0), 
  d_bitblastTimer("theory::bv::BitblastTimer")
{
  StatisticsRegistry::registerStat(&d_numTermClauses);
  StatisticsRegistry::registerStat(&d_numAtomClauses);
  StatisticsRegistry::registerStat(&d_numTerms);
  StatisticsRegistry::registerStat(&d_numAtoms);
  StatisticsRegistry::registerStat(&d_bitblastTimer);
}


Bitblaster::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_numTermClauses);
  StatisticsRegistry::unregisterStat(&d_numAtomClauses);
  StatisticsRegistry::unregisterStat(&d_numTerms);
  StatisticsRegistry::unregisterStat(&d_numAtoms);
  StatisticsRegistry::unregisterStat(&d_bitblastTimer);
}

bool Bitblaster::MinisatNotify::notify(prop::SatLiteral lit) {
  return d_bv->storePropagation(d_cnf->getNode(lit), SUB_BITBLAST);
};

void Bitblaster::MinisatNotify::notify(prop::SatClause& clause) {
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
};

void Bitblaster::MinisatNotify::safePoint() {
  d_bv->d_out->safePoint(); 
}

EqualityStatus Bitblaster::getEqualityStatus(TNode a, TNode b) {

  // We don't want to bit-blast every possibly expensive term for the sake of equality checking
  if (hasBBTerm(a) && hasBBTerm(b)) {

  Bits a_bits, b_bits;
  getBBTerm(a, a_bits);
  getBBTerm(b, b_bits);
  EqualityStatus status = EQUALITY_TRUE_IN_MODEL;
  for (unsigned i = 0; i < a_bits.size(); ++ i) {
    if (d_cnfStream->hasLiteral(a_bits[i]) && d_cnfStream->hasLiteral(b_bits[i])) {
      SatLiteral a_lit = d_cnfStream->getLiteral(a_bits[i]);
      SatValue a_lit_value = d_satSolver->value(a_lit);
      if (a_lit_value != SAT_VALUE_UNKNOWN) {
        SatLiteral b_lit = d_cnfStream->getLiteral(b_bits[i]);
        SatValue b_lit_value = d_satSolver->value(b_lit);
        if (b_lit_value != SAT_VALUE_UNKNOWN) {
          if (a_lit_value != b_lit_value) {
            return EQUALITY_FALSE_IN_MODEL;
          }
        } else {
          status = EQUALITY_UNKNOWN;
        }
      } {
        status = EQUALITY_UNKNOWN;
      }
    } else {
      status = EQUALITY_UNKNOWN;
    }
  }

  return status;

  } else {
    return EQUALITY_UNKNOWN;
  }
}


bool Bitblaster::isSharedTerm(TNode node) {
  return d_bv->d_sharedTermsSet.find(node) != d_bv->d_sharedTermsSet.end(); 
}

bool Bitblaster::hasValue(TNode a) {
  Assert (d_termCache.find(a) != d_termCache.end()); 
  Bits bits = d_termCache[a];
  for (int i = bits.size() -1; i >= 0; --i) {
    SatValue bit_value; 
    if (d_cnfStream->hasLiteral(bits[i])) { 
      SatLiteral bit = d_cnfStream->getLiteral(bits[i]);
      bit_value = d_satSolver->value(bit);
      if (bit_value == SAT_VALUE_UNKNOWN)
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
 * 
 * @return 
 */
Node Bitblaster::getVarValue(TNode a) {
  if (d_termCache.find(a) == d_termCache.end()) {
    Assert(isSharedTerm(a));
    return Node(); 
  }
  Bits bits = d_termCache[a];
  Integer value(0); 
  for (int i = bits.size() -1; i >= 0; --i) {
    SatValue bit_value;
    if (d_cnfStream->hasLiteral(bits[i])) { 
      SatLiteral bit = d_cnfStream->getLiteral(bits[i]);
      bit_value = d_satSolver->value(bit);
      Assert (bit_value != SAT_VALUE_UNKNOWN); 
    } else {
      // the bit is unconstrainted so we can give it an arbitrary value 
      bit_value = SAT_VALUE_FALSE;
    }
    Integer bit_int = bit_value == SAT_VALUE_TRUE ? Integer(1) : Integer(0); 
    value = value * 2 + bit_int;  
  }
  return utils::mkConst(BitVector(bits.size(), value));  
}

void Bitblaster::collectModelInfo(TheoryModel* m) {
  __gnu_cxx::hash_set<TNode, TNodeHashFunction>::iterator it = d_variables.begin();
  for (; it!= d_variables.end(); ++it) {
    TNode var = *it;
    if (Theory::theoryOf(var) == theory::THEORY_BV || isSharedTerm(var))  {
      Node const_value = getVarValue(var);
      if(const_value == Node()) {
        // if the value is unassigned just set it to zero
        const_value = utils::mkConst(BitVector(utils::getSize(var), 0u)); 
      }
      Debug("bitvector-model") << "Bitblaster::collectModelInfo (assert (= "
                                << var << " "
                                << const_value << "))\n";
      m->assertEquality(var, const_value, true); 
    }
  }
}

} /*bv namespace */
} /* theory namespace */
} /* CVC4 namespace*/
