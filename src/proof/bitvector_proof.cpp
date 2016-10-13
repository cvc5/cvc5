/*********************                                                        */
/*! \file bitvector_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Guy Katz, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]

 ** \todo document this file

**/

#include "options/bv_options.h"
#include "options/proof_options.h"
#include "proof/array_proof.h"
#include "proof/bitvector_proof.h"
#include "proof/clause_id.h"
#include "proof/proof_output_channel.h"
#include "proof/proof_utils.h"
#include "proof/sat_proof_implementation.h"
#include "prop/bvminisat/bvminisat.h"
#include "theory/bv/bitblaster_template.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_rewrite_rules.h"

using namespace CVC4::theory;
using namespace CVC4::theory::bv;

namespace CVC4 {

BitVectorProof::BitVectorProof(theory::bv::TheoryBV* bv, TheoryProofEngine* proofEngine)
  : TheoryProof(bv, proofEngine)
  , d_declarations()
  , d_seenBBTerms()
  , d_bbTerms()
  , d_bbAtoms()
  , d_resolutionProof(NULL)
  , d_cnfProof(NULL)
  , d_bitblaster(NULL)
  , d_useConstantLetification(false)
{}

void BitVectorProof::initSatProof(CVC4::BVMinisat::Solver* solver) {
  Assert (d_resolutionProof == NULL);
  d_resolutionProof = new LFSCBVSatProof(solver, "bb", true);
}

void BitVectorProof::initCnfProof(prop::CnfStream* cnfStream,
                                  context::Context* cnf) {
  Assert (d_cnfProof == NULL);
  d_cnfProof = new LFSCCnfProof(cnfStream, cnf, "bb");
  Assert (d_resolutionProof != NULL);
  d_resolutionProof->setCnfProof(d_cnfProof);

  // true and false have to be setup in a special way
  Node true_node = NodeManager::currentNM()->mkConst<bool>(true);
  Node false_node = NodeManager::currentNM()->mkConst<bool>(false).notNode();

  d_cnfProof->pushCurrentAssertion(true_node);
  d_cnfProof->pushCurrentDefinition(true_node);
  d_cnfProof->registerConvertedClause(d_resolutionProof->getTrueUnit());
  d_cnfProof->popCurrentAssertion();
  d_cnfProof->popCurrentDefinition();

  d_cnfProof->pushCurrentAssertion(false_node);
  d_cnfProof->pushCurrentDefinition(false_node);
  d_cnfProof->registerConvertedClause(d_resolutionProof->getFalseUnit());
  d_cnfProof->popCurrentAssertion();
  d_cnfProof->popCurrentDefinition();
}

void BitVectorProof::setBitblaster(bv::TBitblaster<Node>* bb) {
  Assert (d_bitblaster == NULL);
  d_bitblaster = bb;
}

BVSatProof* BitVectorProof::getSatProof() {
  Assert (d_resolutionProof != NULL);
  return d_resolutionProof;
}

void BitVectorProof::registerTermBB(Expr term) {
  Debug("pf::bv") << "BitVectorProof::registerTermBB( " << term << " )" << std::endl;

  if (d_seenBBTerms.find(term) != d_seenBBTerms.end())
    return;

  d_seenBBTerms.insert(term);
  d_bbTerms.push_back(term);

  // If this term gets used in the final proof, we will want to register it. However,
  // we don't know this at this point; and when the theory proof engine sees it, if it belongs
  // to another theory, it won't register it with this proof. So, we need to tell the
  // engine to inform us.

  if (theory::Theory::theoryOf(term) != theory::THEORY_BV) {
    Debug("pf::bv") << "\tMarking term " << term << " for future BV registration" << std::endl;
    d_proofEngine->markTermForFutureRegistration(term, theory::THEORY_BV);
  }
}

void BitVectorProof::registerAtomBB(Expr atom, Expr atom_bb) {
  Debug("pf::bv") << "BitVectorProof::registerAtomBB( " << atom << ", " << atom_bb << " )" << std::endl;

  Expr def = atom.iffExpr(atom_bb);
  d_bbAtoms.insert(std::make_pair(atom, def));
  registerTerm(atom);

  // Register the atom's terms for bitblasting
  registerTermBB(atom[0]);
  registerTermBB(atom[1]);
}

void BitVectorProof::registerTerm(Expr term) {
  Debug("pf::bv") << "BitVectorProof::registerTerm( " << term << " )" << std::endl;

  if (options::lfscLetification() && term.isConst()) {
    if (d_constantLetMap.find(term) == d_constantLetMap.end()) {
      std::ostringstream name;
      name << "letBvc" << d_constantLetMap.size();
      d_constantLetMap[term] = name.str();
    }
  }

  d_usedBB.insert(term);

  if (Theory::isLeafOf(term, theory::THEORY_BV) &&
      !term.isConst()) {
    d_declarations.insert(term);
  }

  Debug("pf::bv") << "Going to register children: " << std::endl;
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    Debug("pf::bv") << "\t" << term[i] << std::endl;
  }

  // don't care about parametric operators for bv?
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
     d_proofEngine->registerTerm(term[i]);
  }
}

std::string BitVectorProof::getBBTermName(Expr expr) {
  Debug("pf::bv") << "BitVectorProof::getBBTermName( " << expr << " ) = bt" << expr.getId() << std::endl;
  std::ostringstream os;
  os << "bt"<< expr.getId();
  return os.str();
}

void BitVectorProof::startBVConflict(CVC4::BVMinisat::Solver::TCRef cr) {
  d_resolutionProof->startResChain(cr);
}

void BitVectorProof::startBVConflict(CVC4::BVMinisat::Solver::TLit lit) {
  d_resolutionProof->startResChain(lit);
}

void BitVectorProof::endBVConflict(const CVC4::BVMinisat::Solver::TLitVec& confl) {
  Debug("pf::bv") << "BitVectorProof::endBVConflict called" << std::endl;

  std::vector<Expr> expr_confl;
  for (int i = 0; i < confl.size(); ++i) {
    prop::SatLiteral lit = prop::BVMinisatSatSolver::toSatLiteral(confl[i]);
    Expr atom = d_cnfProof->getAtom(lit.getSatVariable()).toExpr();
    Expr expr_lit = lit.isNegated() ? atom.notExpr() : atom;
    expr_confl.push_back(expr_lit);
  }

  Expr conflict = utils::mkSortedExpr(kind::OR, expr_confl);
  Debug("pf::bv") << "Make conflict for " << conflict << std::endl;

  if (d_bbConflictMap.find(conflict) != d_bbConflictMap.end()) {
    Debug("pf::bv") << "Abort...already conflict for " << conflict << std::endl;
    // This can only happen when we have eager explanations in the bv solver
    // if we don't get to propagate p before ~p is already asserted
    d_resolutionProof->cancelResChain();
    return;
  }

  // we don't need to check for uniqueness in the sat solver then
  ClauseId clause_id = d_resolutionProof->registerAssumptionConflict(confl);
  d_bbConflictMap[conflict] = clause_id;
  d_resolutionProof->endResChain(clause_id);
  Debug("pf::bv") << "BitVectorProof::endBVConflict id" <<clause_id<< " => " << conflict << "\n";
  d_isAssumptionConflict = false;
}

void BitVectorProof::finalizeConflicts(std::vector<Expr>& conflicts) {

  if (options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER) {
    Debug("pf::bv") << "Construct full proof." << std::endl;
    d_resolutionProof->constructProof();
    return;
  }

  for (unsigned i = 0; i < conflicts.size(); ++i) {
    Expr confl = conflicts[i];
    Debug("pf::bv") << "Finalize conflict #" << i << ": " << confl << std::endl;

    // Special case: if the conflict has a (true) or a (not false) in it, it is trivial...
    bool ignoreConflict = false;
    if ((confl.isConst() && confl.getConst<bool>()) ||
        (confl.getKind() == kind::NOT && confl[0].isConst() && !confl[0].getConst<bool>())) {
      ignoreConflict = true;
    } else if (confl.getKind() == kind::OR) {
      for (unsigned k = 0; k < confl.getNumChildren(); ++k) {
        if ((confl[k].isConst() && confl[k].getConst<bool>()) ||
            (confl[k].getKind() == kind::NOT && confl[k][0].isConst() && !confl[k][0].getConst<bool>())) {
          ignoreConflict = true;
        }
      }
    }
    if (ignoreConflict) {
      Debug("pf::bv") << "Ignoring conflict due to (true) or (not false)" << std::endl;
      continue;
    }

    if (d_bbConflictMap.find(confl) != d_bbConflictMap.end()) {
      ClauseId id = d_bbConflictMap[confl];
      d_resolutionProof->collectClauses(id);
    } else {
      // There is no exact match for our conflict, but maybe it is a subset of another conflict
      ExprToClauseId::const_iterator it;
      bool matchFound = false;
      for (it = d_bbConflictMap.begin(); it != d_bbConflictMap.end(); ++it) {
        Expr possibleMatch = it->first;
        if (possibleMatch.getKind() != kind::OR) {
          // This is a single-node conflict. If this node is in the conflict we're trying to prove,
          // we have a match.
          for (unsigned k = 0; k < confl.getNumChildren(); ++k) {
            if (confl[k] == possibleMatch) {
              matchFound = true;
              d_resolutionProof->collectClauses(it->second);
              break;
            }
          }
        } else {
          if (possibleMatch.getNumChildren() > confl.getNumChildren())
            continue;

          unsigned k = 0;
          bool matching = true;
          for (unsigned j = 0; j < possibleMatch.getNumChildren(); ++j) {
            // j is the index in possibleMatch
            // k is the index in confl
            while (k < confl.getNumChildren() && confl[k] != possibleMatch[j]) {
              ++k;
            }
            if (k == confl.getNumChildren()) {
              // We couldn't find a match for possibleMatch[j], so not a match
              matching = false;
              break;
            }
          }

          if (matching) {
            Debug("pf::bv") << "Collecting info from a sub-conflict" << std::endl;
            d_resolutionProof->collectClauses(it->second);
            matchFound = true;
            break;
          }
        }
      }

      if (!matchFound) {
        Debug("pf::bv") << "Do not collect clauses for " << confl << std::endl
                        << "Dumping existing conflicts:" << std::endl;

        i = 0;
        for (it = d_bbConflictMap.begin(); it != d_bbConflictMap.end(); ++it) {
          ++i;
          Debug("pf::bv") << "\tConflict #" << i << ": " << it->first << std::endl;
        }

        Unreachable();
      }
    }
  }
}

void LFSCBitVectorProof::printOwnedTerm(Expr term, std::ostream& os, const ProofLetMap& map) {
  Debug("pf::bv") << std::endl << "(pf::bv) LFSCBitVectorProof::printOwnedTerm( " << term << " ), theory is: "
                  << Theory::theoryOf(term) << std::endl;

  Assert (Theory::theoryOf(term) == THEORY_BV);

  // peel off eager bit-blasting trick
  if (term.getKind() == kind::BITVECTOR_EAGER_ATOM) {
    d_proofEngine->printBoundTerm(term[0], os, map);
    return;
  }

  switch (term.getKind()) {
  case kind::CONST_BITVECTOR : {
    printConstant(term, os);
    return;
  }
  case kind::BITVECTOR_AND :
  case kind::BITVECTOR_OR :
  case kind::BITVECTOR_XOR :
  case kind::BITVECTOR_NAND :
  case kind::BITVECTOR_NOR :
  case kind::BITVECTOR_XNOR :
  case kind::BITVECTOR_COMP :
  case kind::BITVECTOR_MULT :
  case kind::BITVECTOR_PLUS :
  case kind::BITVECTOR_SUB :
  case kind::BITVECTOR_UDIV :
  case kind::BITVECTOR_UREM :
  case kind::BITVECTOR_UDIV_TOTAL :
  case kind::BITVECTOR_UREM_TOTAL :
  case kind::BITVECTOR_SDIV :
  case kind::BITVECTOR_SREM :
  case kind::BITVECTOR_SMOD :
  case kind::BITVECTOR_SHL :
  case kind::BITVECTOR_LSHR :
  case kind::BITVECTOR_ASHR :
  case kind::BITVECTOR_CONCAT : {
    printOperatorNary(term, os, map);
    return;
  }
  case kind::BITVECTOR_NEG :
  case kind::BITVECTOR_NOT :
  case kind::BITVECTOR_ROTATE_LEFT :
  case kind::BITVECTOR_ROTATE_RIGHT : {
    printOperatorUnary(term, os, map);
    return;
  }
  case kind::EQUAL :
  case kind::BITVECTOR_ULT :
  case kind::BITVECTOR_ULE :
  case kind::BITVECTOR_UGT :
  case kind::BITVECTOR_UGE :
  case kind::BITVECTOR_SLT :
  case kind::BITVECTOR_SLE :
  case kind::BITVECTOR_SGT :
  case kind::BITVECTOR_SGE : {
    printPredicate(term, os, map);
    return;
  }
  case kind::BITVECTOR_EXTRACT :
  case kind::BITVECTOR_REPEAT :
  case kind::BITVECTOR_ZERO_EXTEND :
  case kind::BITVECTOR_SIGN_EXTEND : {
    printOperatorParametric(term, os, map);
    return;
  }
  case kind::BITVECTOR_BITOF : {
    printBitOf(term, os, map);
    return;
  }

  case kind::VARIABLE: {
    os << "(a_var_bv " << utils::getSize(term)<< " " << ProofManager::sanitize(term) << ")";
    return;
  }

  case kind::SKOLEM: {

    // TODO: we need to distinguish between "real" skolems (e.g. from array) and "fake" skolems,
    // like ITE terms. Is there a more elegant way?

    if (ProofManager::getSkolemizationManager()->isSkolem(term)) {
      os << ProofManager::sanitize(term);
    } else {
      os << "(a_var_bv " << utils::getSize(term)<< " " << ProofManager::sanitize(term) << ")";
    }
    return;
  }

  default:
    Unreachable();
  }
}

void LFSCBitVectorProof::printBitOf(Expr term, std::ostream& os, const ProofLetMap& map) {
  Assert (term.getKind() == kind::BITVECTOR_BITOF);
  unsigned bit = term.getOperator().getConst<BitVectorBitOf>().bitIndex;
  Expr var = term[0];

  Debug("pf::bv") << "LFSCBitVectorProof::printBitOf( " << term << " ), "
                  << "bit = " << bit
                  << ", var = " << var << std::endl;

  os << "(bitof ";
  os << d_exprToVariableName[var];
  os << " " << bit << ")";
}

void LFSCBitVectorProof::printConstant(Expr term, std::ostream& os) {
  Assert (term.isConst());
  os << "(a_bv " << utils::getSize(term) << " ";

  if (d_useConstantLetification) {
    os << d_constantLetMap[term] << ")";
  } else {
    std::ostringstream paren;
    int size = utils::getSize(term);
    for (int i = size - 1; i >= 0; --i) {
      os << "(bvc ";
      os << (utils::getBit(term, i) ? "b1" : "b0") <<" ";
      paren << ")";
    }
    os << " bvn)";
    os << paren.str();
  }
}

void LFSCBitVectorProof::printOperatorNary(Expr term, std::ostream& os, const ProofLetMap& map) {
  std::string op = utils::toLFSCKind(term.getKind());
  std::ostringstream paren;
  std::string holes = term.getKind() == kind::BITVECTOR_CONCAT ? "_ _ " : "";
  unsigned size = term.getKind() == kind::BITVECTOR_CONCAT? utils::getSize(term) :
                                                            utils::getSize(term[0]); // cause of COMP

  for (unsigned i = 0; i < term.getNumChildren() - 1; ++i) {
    os <<"("<< op <<" " <<  size <<" " << holes;
  }
  d_proofEngine->printBoundTerm(term[0], os, map);
  os <<" ";
  for (unsigned i = 1; i < term.getNumChildren(); ++i) {
    d_proofEngine->printBoundTerm(term[i], os, map);
    os << ")";
  }
}

void LFSCBitVectorProof::printOperatorUnary(Expr term, std::ostream& os, const ProofLetMap& map) {
  os <<"(";
  os << utils::toLFSCKind(term.getKind()) << " " << utils::getSize(term) <<" ";
  os << " ";
  d_proofEngine->printBoundTerm(term[0], os, map);
  os <<")";
}

void LFSCBitVectorProof::printPredicate(Expr term, std::ostream& os, const ProofLetMap& map) {
  os <<"(";
  os << utils::toLFSCKind(term.getKind()) << " " << utils::getSize(term[0]) <<" ";
  os << " ";
  d_proofEngine->printBoundTerm(term[0], os, map);
  os << " ";
  d_proofEngine->printBoundTerm(term[1], os, map);
  os <<")";
}

void LFSCBitVectorProof::printOperatorParametric(Expr term, std::ostream& os, const ProofLetMap& map) {
  os <<"(";
  os << utils::toLFSCKind(term.getKind()) << " " << utils::getSize(term) <<" ";
  os <<" ";
  if (term.getKind() == kind::BITVECTOR_REPEAT) {
    unsigned amount = term.getOperator().getConst<BitVectorRepeat>().repeatAmount;
    os << amount <<" _ ";
  }
  if (term.getKind() == kind::BITVECTOR_SIGN_EXTEND) {
    unsigned amount = term.getOperator().getConst<BitVectorSignExtend>().signExtendAmount;
    os << amount <<" _ ";
  }

  if (term.getKind() == kind::BITVECTOR_ZERO_EXTEND) {
    unsigned amount = term.getOperator().getConst<BitVectorZeroExtend>().zeroExtendAmount;
    os << amount<<" _ ";
  }
  if (term.getKind() == kind::BITVECTOR_EXTRACT) {
    unsigned low = utils::getExtractLow(term);
    unsigned high = utils::getExtractHigh(term);
    os << high <<" " << low << " " << utils::getSize(term[0]);
  }
  os <<" ";
  Assert (term.getNumChildren() == 1);
  d_proofEngine->printBoundTerm(term[0], os, map);
  os <<")";
}

void LFSCBitVectorProof::printOwnedSort(Type type, std::ostream& os) {
  Debug("pf::bv") << std::endl << "(pf::bv) LFSCBitVectorProof::printOwnedSort( " << type << " )" << std::endl;
  Assert (type.isBitVector());
  unsigned width = utils::getSize(type);
  os << "(BitVec " << width << ")";
}

void LFSCBitVectorProof::printTheoryLemmaProof(std::vector<Expr>& lemma, std::ostream& os, std::ostream& paren, const ProofLetMap& map) {
  Debug("pf::bv") << "(pf::bv) LFSCBitVectorProof::printTheoryLemmaProof called" << std::endl;
  Expr conflict = utils::mkSortedExpr(kind::OR, lemma);
  Debug("pf::bv") << "\tconflict = " << conflict << std::endl;

  if (d_bbConflictMap.find(conflict) != d_bbConflictMap.end()) {
    std::ostringstream lemma_paren;
    for (unsigned i = 0; i < lemma.size(); ++i) {
      Expr lit = lemma[i];

      if (lit.getKind() == kind::NOT) {
        os << "(intro_assump_t _ _ _ ";
      } else {
        os << "(intro_assump_f _ _ _ ";
      }
      lemma_paren <<")";
      // print corresponding literal in main sat solver
      ProofManager* pm = ProofManager::currentPM();
      CnfProof* cnf = pm->getCnfProof();
      prop::SatLiteral main_lit = cnf->getLiteral(lit);
      os << pm->getLitName(main_lit);
      os <<" ";
      // print corresponding literal in bv sat solver
      prop::SatVariable bb_var = d_cnfProof->getLiteral(lit).getSatVariable();
      os << pm->getAtomName(bb_var, "bb");
      os <<"(\\ unit"<<bb_var<<"\n";
      lemma_paren <<")";
    }
    Expr lem = utils::mkOr(lemma);
    Assert (d_bbConflictMap.find(lem) != d_bbConflictMap.end());
    ClauseId lemma_id = d_bbConflictMap[lem];
    d_resolutionProof->printAssumptionsResolution(lemma_id, os, lemma_paren);
    os <<lemma_paren.str();
  } else {

    Debug("pf::bv") << "Found a non-recorded conflict. Looking for a matching sub-conflict..."
                    << std::endl;

    bool matching;

    ExprToClauseId::const_iterator it;
    unsigned i = 0;
    for (it = d_bbConflictMap.begin(); it != d_bbConflictMap.end(); ++it) {
      // Our conflict is sorted, and the records are also sorted.
      ++i;
      Expr possibleMatch = it->first;

      if (possibleMatch.getKind() != kind::OR) {
        // This is a single-node conflict. If this node is in the conflict we're trying to prove,
        // we have a match.
        matching = false;

        for (unsigned k = 0; k < conflict.getNumChildren(); ++k) {
          if (conflict[k] == possibleMatch) {
            matching = true;
            break;
          }
        }
      } else {
        if (possibleMatch.getNumChildren() > conflict.getNumChildren())
          continue;

        unsigned k = 0;

        matching = true;
        for (unsigned j = 0; j < possibleMatch.getNumChildren(); ++j) {
          // j is the index in possibleMatch
          // k is the index in conflict
          while (k < conflict.getNumChildren() && conflict[k] != possibleMatch[j]) {
            ++k;
          }
          if (k == conflict.getNumChildren()) {
            // We couldn't find a match for possibleMatch[j], so not a match
            matching = false;
            break;
          }
        }
      }

      if (matching) {
        Debug("pf::bv") << "Found a match with conflict #" << i << ": " << std::endl << possibleMatch << std::endl;
        // The rest is just a copy of the usual handling, if a precise match is found.
        // We only use the literals that appear in the matching conflict, though, and not in the
        // original lemma - as these may not have even been bit blasted!
        std::ostringstream lemma_paren;

        if (possibleMatch.getKind() == kind::OR) {
          for (unsigned i = 0; i < possibleMatch.getNumChildren(); ++i) {
            Expr lit = possibleMatch[i];

            if (lit.getKind() == kind::NOT) {
              os << "(intro_assump_t _ _ _ ";
            } else {
              os << "(intro_assump_f _ _ _ ";
            }
            lemma_paren <<")";
            // print corresponding literal in main sat solver
            ProofManager* pm = ProofManager::currentPM();
            CnfProof* cnf = pm->getCnfProof();
            prop::SatLiteral main_lit = cnf->getLiteral(lit);
            os << pm->getLitName(main_lit);
            os <<" ";
            // print corresponding literal in bv sat solver
            prop::SatVariable bb_var = d_cnfProof->getLiteral(lit).getSatVariable();
            os << pm->getAtomName(bb_var, "bb");
            os <<"(\\ unit"<<bb_var<<"\n";
            lemma_paren <<")";
          }
        } else {
          // The conflict only consists of one node, either positive or negative.
          Expr lit = possibleMatch;
          if (lit.getKind() == kind::NOT) {
            os << "(intro_assump_t _ _ _ ";
          } else {
            os << "(intro_assump_f _ _ _ ";
          }
          lemma_paren <<")";
          // print corresponding literal in main sat solver
          ProofManager* pm = ProofManager::currentPM();
          CnfProof* cnf = pm->getCnfProof();
          prop::SatLiteral main_lit = cnf->getLiteral(lit);
          os << pm->getLitName(main_lit);
          os <<" ";
          // print corresponding literal in bv sat solver
          prop::SatVariable bb_var = d_cnfProof->getLiteral(lit).getSatVariable();
          os << pm->getAtomName(bb_var, "bb");
          os <<"(\\ unit"<<bb_var<<"\n";
          lemma_paren <<")";
        }

        ClauseId lemma_id = it->second;
        d_resolutionProof->printAssumptionsResolution(lemma_id, os, lemma_paren);
        os <<lemma_paren.str();

        return;
      }
    }

    // We failed to find a matching sub conflict. The last hope is that the
    // conflict has a FALSE assertion in it; this can happen in some corner cases,
    // where the FALSE is the result of a rewrite.

    for (unsigned i = 0; i < lemma.size(); ++i) {
      if (lemma[i].getKind() == kind::NOT && lemma[i][0] == utils::mkFalse()) {
        Debug("pf::bv") << "Lemma has a (not false) literal" << std::endl;
        os << "(clausify_false ";
        os << ProofManager::getLitName(lemma[i]);
        os << ")";
        return;
      }
    }

    Debug("pf::bv") << "Failed to find a matching sub-conflict..." << std::endl
                    << "Dumping existing conflicts:" << std::endl;

    i = 0;
    for (it = d_bbConflictMap.begin(); it != d_bbConflictMap.end(); ++it) {
      ++i;
      Debug("pf::bv") << "\tConflict #" << i << ": " << it->first << std::endl;
    }

    Unreachable();
  }
}

void LFSCBitVectorProof::printSortDeclarations(std::ostream& os, std::ostream& paren) {
  // Nothing to do here at this point.
}

void LFSCBitVectorProof::printTermDeclarations(std::ostream& os, std::ostream& paren) {
  ExprSet::const_iterator it = d_declarations.begin();
  ExprSet::const_iterator end = d_declarations.end();
  for (; it != end; ++it) {
    if ((it->isVariable() || it->isConst()) && !ProofManager::getSkolemizationManager()->isSkolem(*it)) {
      d_exprToVariableName[*it] = ProofManager::sanitize(*it);
    } else {
      std::string newAlias = assignAlias(*it);
      d_exprToVariableName[*it] = newAlias;
    }

    os << "(% " << d_exprToVariableName[*it] <<" var_bv" << "\n";
    paren <<")";
  }
}

void LFSCBitVectorProof::printDeferredDeclarations(std::ostream& os, std::ostream& paren) {
  if (options::lfscLetification()) {
    os << std::endl << ";; BV const letification\n" << std::endl;
    std::map<Expr,std::string>::const_iterator it;
    for (it = d_constantLetMap.begin(); it != d_constantLetMap.end(); ++it) {
      os << "\n(@ " << it->second << " ";
      std::ostringstream localParen;
      int size = utils::getSize(it->first);
      for (int i = size - 1; i >= 0; --i) {
        os << "(bvc ";
        os << (utils::getBit(it->first, i) ? "b1" : "b0") << " ";
        localParen << ")";
      }
      os << "bvn";
      os << localParen.str();
      paren << ")";
    }
    os << std::endl;

    d_useConstantLetification = true;
  }
}

void LFSCBitVectorProof::printAliasingDeclarations(std::ostream& os, std::ostream& paren, const ProofLetMap &globalLetMap) {
  // Print "trust" statements to bind complex bv variables to their associated terms

  ExprToString::const_iterator it = d_assignedAliases.begin();
  ExprToString::const_iterator end = d_assignedAliases.end();

  for (; it != end; ++it) {
    Debug("pf::bv") << "Printing aliasing declaration for: " << *it << std::endl;
    std::stringstream declaration;
    declaration << ".fbvd" << d_aliasToBindDeclaration.size();
    d_aliasToBindDeclaration[it->second] = declaration.str();

    os << "(th_let_pf _ ";

    os << "(trust_f ";
    os << "(= (BitVec " << utils::getSize(it->first) << ") ";
    os << "(a_var_bv " << utils::getSize(it->first) << " " << it->second << ") ";
    d_proofEngine->printBoundTerm(it->first, os, globalLetMap);
    os << ")) ";
    os << "(\\ "<< d_aliasToBindDeclaration[it->second] << "\n";
    paren << "))";
  }

  os << "\n";
}

void LFSCBitVectorProof::printTermBitblasting(Expr term, std::ostream& os) {
  // TODO: once we have the operator elimination rules remove those that we
  // eliminated
  Assert (term.getType().isBitVector());
  Kind kind = term.getKind();

  if (Theory::isLeafOf(term, theory::THEORY_BV) && !term.isConst()) {
    // A term is a leaf if it has no children, or if it belongs to another theory
    os << "(bv_bbl_var " << utils::getSize(term) << " " << d_exprToVariableName[term];
    os << " _)";
    return;
  }

  switch(kind) {
  case kind::CONST_BITVECTOR : {
    os << "(bv_bbl_const "<< utils::getSize(term) <<" _ ";
    std::ostringstream paren;
    int size = utils::getSize(term);
    if (d_useConstantLetification) {
      os << d_constantLetMap[term] << ")";
    } else {
      for (int i = size - 1; i>= 0; --i) {
        os << "(bvc ";
        os << (utils::getBit(term, i) ? "b1" : "b0") <<" ";
        paren << ")";
      }
      os << " bvn)";
      os << paren.str();
    }
    return;
  }

  case kind::BITVECTOR_AND :
  case kind::BITVECTOR_OR :
  case kind::BITVECTOR_XOR :
  case kind::BITVECTOR_NAND :
  case kind::BITVECTOR_NOR :
  case kind::BITVECTOR_XNOR :
  case kind::BITVECTOR_COMP :
  case kind::BITVECTOR_MULT :
  case kind::BITVECTOR_PLUS :
  case kind::BITVECTOR_SUB :
  case kind::BITVECTOR_CONCAT : {
    Debug("pf::bv") << "Bitblasing kind = " << kind << std::endl;

    for (int i = term.getNumChildren() - 1; i > 0; --i) {
      os <<"(bv_bbl_"<< utils::toLFSCKind(kind);

      if (kind == kind::BITVECTOR_CONCAT) {
        os << " " << utils::getSize(term) << " _";
      }
      os << " _ _ _ _ _ _ ";
    }

    os << getBBTermName(term[0]) << " ";

    for (unsigned i = 1; i < term.getNumChildren(); ++i) {
      os << getBBTermName(term[i]);
      os << ") ";
    }
    return;
  }

  case kind::BITVECTOR_NEG :
  case kind::BITVECTOR_NOT :
  case kind::BITVECTOR_ROTATE_LEFT :
  case kind::BITVECTOR_ROTATE_RIGHT : {
    os << "(bv_bbl_"<<utils::toLFSCKind(kind);
    os << " _ _ _ _ ";
    os << getBBTermName(term[0]);
    os << ")";
    return;
  }
  case kind::BITVECTOR_EXTRACT : {
    os <<"(bv_bbl_"<<utils::toLFSCKind(kind);

    os << " " << utils::getSize(term) << " ";
    os << utils::getExtractHigh(term) << " ";
    os << utils::getExtractLow(term) << " ";
    os << " _ _ _ _ ";

    os << getBBTermName(term[0]);
    os <<")";
    return;
  }
  case kind::BITVECTOR_REPEAT :
  case kind::BITVECTOR_ZERO_EXTEND :
  case kind::BITVECTOR_SIGN_EXTEND : {
    os << "(bv_bbl_" << utils::toLFSCKind(kind) << " ";
    os << utils::getSize(term) << " ";
    if (term.getKind() == kind::BITVECTOR_REPEAT) {
      unsigned amount = term.getOperator().getConst<BitVectorRepeat>().repeatAmount;
      os << amount;
    }
    if (term.getKind() == kind::BITVECTOR_SIGN_EXTEND) {
      unsigned amount = term.getOperator().getConst<BitVectorSignExtend>().signExtendAmount;
      os << amount;
    }

    if (term.getKind() == kind::BITVECTOR_ZERO_EXTEND) {
      unsigned amount = term.getOperator().getConst<BitVectorZeroExtend>().zeroExtendAmount;
      os << amount;
    }

    os <<" _ _ _ _ ";
    os << getBBTermName(term[0]);
    os <<")";
    return;
  }
  case kind::BITVECTOR_UDIV :
  case kind::BITVECTOR_UREM :
  case kind::BITVECTOR_UDIV_TOTAL :
  case kind::BITVECTOR_UREM_TOTAL :
  case kind::BITVECTOR_SDIV :
  case kind::BITVECTOR_SREM :
  case kind::BITVECTOR_SMOD :
  case kind::BITVECTOR_SHL :
  case kind::BITVECTOR_LSHR :
  case kind::BITVECTOR_ASHR : {
 	// these are terms for which bit-blasting is not supported yet
    std::ostringstream paren;
    os <<"(trust_bblast_term _ ";
    paren <<")";
    d_proofEngine->printLetTerm(term, os);
    os <<" ";
    std::vector<Node> bits;
    d_bitblaster->bbTerm(term, bits);

    for (int i = utils::getSize(term) - 1; i >= 0; --i) {
      os << "(bbltc ";
      d_proofEngine->printLetTerm((bits[i]).toExpr(), os);
      paren << ")";
    }
    os << "bbltn" << paren.str();
    return;
  }

  default:
    Unreachable("LFSCBitVectorProof Unknown operator");
  }
}

void LFSCBitVectorProof::printAtomBitblasting(Expr atom, std::ostream& os, bool swap) {
  Kind kind = atom.getKind();
  switch(kind) {
  case kind::BITVECTOR_ULT :
  case kind::BITVECTOR_ULE :
  case kind::BITVECTOR_UGT :
  case kind::BITVECTOR_UGE :
  case kind::BITVECTOR_SLT :
  case kind::BITVECTOR_SLE :
  case kind::BITVECTOR_SGT :
  case kind::BITVECTOR_SGE :
  case kind::EQUAL: {
    Debug("pf::bv") << "Bitblasing kind = " << kind << std::endl;

    os << "(bv_bbl_" << utils::toLFSCKind(atom.getKind());

    if (swap) {os << "_swap";}

    os << " _ _ _ _ _ _ ";
    os << getBBTermName(atom[0]);
    os << " ";
    os << getBBTermName(atom[1]);
    os << ")";

    return;
  }
  default:
    Unreachable("LFSCBitVectorProof Unknown atom kind");
  }
}

void LFSCBitVectorProof::printAtomBitblastingToFalse(Expr atom, std::ostream& os) {
  Assert(atom.getKind() == kind::EQUAL);

  os << "(bv_bbl_=_false";
  os << " _ _ _ _ _ _ ";
  os << getBBTermName(atom[0]);

  os << " ";

  os << getBBTermName(atom[1]);

  os << ")";
}

void LFSCBitVectorProof::printBitblasting(std::ostream& os, std::ostream& paren) {
  // bit-blast terms
  {
    Debug("pf::bv") << "LFSCBitVectorProof::printBitblasting: the bitblasted terms are: " << std::endl;
    std::vector<Expr>::const_iterator it = d_bbTerms.begin();
    std::vector<Expr>::const_iterator end = d_bbTerms.end();

    Assert(options::bitblastMode() != theory::bv::BITBLAST_MODE_EAGER);

    for (; it != end; ++it) {
      if (d_usedBB.find(*it) == d_usedBB.end()) {
        Debug("pf::bv") << "\t" << *it << "\t(UNUSED)" << std::endl;
      } else {
        Debug("pf::bv") << "\t" << *it << std::endl;
      }
    }

    Debug("pf::bv") << std::endl;
  }

  std::vector<Expr>::const_iterator it = d_bbTerms.begin();
  std::vector<Expr>::const_iterator end = d_bbTerms.end();
  for (; it != end; ++it) {
    if (d_usedBB.find(*it) == d_usedBB.end() &&
        options::bitblastMode() != theory::bv::BITBLAST_MODE_EAGER)
      continue;

    // Is this term has an alias, we inject it through the decl_bblast statement
    if (hasAlias(*it)) {
      os << "(decl_bblast_with_alias _ _ _ _ ";
      printTermBitblasting(*it, os);
      os << " " << d_aliasToBindDeclaration[d_assignedAliases[*it]] << " ";
      os << "(\\ "<< getBBTermName(*it);
      os << "\n";
      paren <<"))";
    } else {
      os << "(decl_bblast _ _ _ ";
      printTermBitblasting(*it, os);
      os << "(\\ "<< getBBTermName(*it);
      os << "\n";
      paren <<"))";
    }
  }
  // bit-blast atoms
  ExprToExpr::const_iterator ait = d_bbAtoms.begin();
  ExprToExpr::const_iterator aend = d_bbAtoms.end();
  for (; ait != aend; ++ait) {
    if (d_usedBB.find(ait->first) == d_usedBB.end() &&
        options::bitblastMode() != theory::bv::BITBLAST_MODE_EAGER)
      continue;

    os << "(th_let_pf _ ";
    if (ait->first.getKind() == kind::CONST_BOOLEAN) {
      bool val = ait->first.getConst<bool>();
      os << "(iff_symm " << (val ? "true" : "false" ) << ")";
    } else {
      Assert(ait->first == ait->second[0]);

      bool swap = false;
      if (ait->first.getKind() == kind::EQUAL) {
        Expr bitwiseEquivalence = ait->second[1];
        if ((bitwiseEquivalence.getKind() == kind::CONST_BOOLEAN) && !bitwiseEquivalence.getConst<bool>()) {
          printAtomBitblastingToFalse(ait->first, os);
        } else {
          if (bitwiseEquivalence.getKind() != kind::AND) {
            // Just one bit
            if (bitwiseEquivalence.getNumChildren() > 0 && bitwiseEquivalence[0].getKind() == kind::BITVECTOR_BITOF) {
              swap = (ait->first[1] == bitwiseEquivalence[0][0]);
            }
          } else {
            // Multiple bits
            if (bitwiseEquivalence[0].getNumChildren() > 0 &&
                bitwiseEquivalence[0][0].getKind() == kind::BITVECTOR_BITOF) {
              swap = (ait->first[1] == bitwiseEquivalence[0][0][0]);
            } else if (bitwiseEquivalence[0].getNumChildren() > 0 &&
                       bitwiseEquivalence[0][1].getKind() == kind::BITVECTOR_BITOF) {
              swap = (ait->first[0] == bitwiseEquivalence[0][1][0]);
            }
          }

          printAtomBitblasting(ait->first, os, swap);
        }
      } else {
        printAtomBitblasting(ait->first, os, swap);
      }
    }

    os <<"(\\ " << ProofManager::getPreprocessedAssertionName(ait->second) <<"\n";
    paren <<"))";
  }
}

void LFSCBitVectorProof::calculateAtomsInBitblastingProof() {
  // Collect the input clauses used
  IdToSatClause used_lemmas;
  IdToSatClause used_inputs;
  d_resolutionProof->collectClausesUsed(used_inputs, used_lemmas);
  d_cnfProof->collectAtomsForClauses(used_inputs, d_atomsInBitblastingProof);
  Assert(used_lemmas.empty());
}

const std::set<Node>* LFSCBitVectorProof::getAtomsInBitblastingProof() {
  return &d_atomsInBitblastingProof;
}

void LFSCBitVectorProof::printResolutionProof(std::ostream& os,
                                              std::ostream& paren,
                                              ProofLetMap& letMap) {
  // print mapping between theory atoms and internal SAT variables
  os << std::endl << ";; BB atom mapping\n" << std::endl;

  std::set<Node>::iterator atomIt;
  Debug("pf::bv") << std::endl << "BV Dumping atoms from inputs: " << std::endl << std::endl;
  for (atomIt = d_atomsInBitblastingProof.begin(); atomIt != d_atomsInBitblastingProof.end(); ++atomIt) {
    Debug("pf::bv") << "\tAtom: " << *atomIt << std::endl;
  }
  Debug("pf::bv") << std::endl;

  // first print bit-blasting
  printBitblasting(os, paren);

  // print CNF conversion proof for bit-blasted facts
  IdToSatClause used_lemmas;
  IdToSatClause used_inputs;
  d_resolutionProof->collectClausesUsed(used_inputs, used_lemmas);

  d_cnfProof->printAtomMapping(d_atomsInBitblastingProof, os, paren, letMap);
  os << std::endl << ";; Bit-blasting definitional clauses \n" << std::endl;
  for (IdToSatClause::iterator it = used_inputs.begin();
       it != used_inputs.end(); ++it) {
    d_cnfProof->printCnfProofForClause(it->first, it->second, os, paren);
  }

  os << std::endl << " ;; Bit-blasting learned clauses \n" << std::endl;
  d_resolutionProof->printResolutions(os, paren);
}

std::string LFSCBitVectorProof::assignAlias(Expr expr) {
  Assert(d_exprToVariableName.find(expr) == d_exprToVariableName.end());

  std::stringstream ss;
  ss << "fbv" << d_assignedAliases.size();
  Debug("pf::bv") << "assignAlias( " << expr << ") = " << ss.str() << std::endl;
  d_assignedAliases[expr] = ss.str();
  return ss.str();
}

bool LFSCBitVectorProof::hasAlias(Expr expr) {
  return d_assignedAliases.find(expr) != d_assignedAliases.end();
}

void LFSCBitVectorProof::printConstantDisequalityProof(std::ostream& os, Expr c1, Expr c2, const ProofLetMap &globalLetMap) {
  Assert (c1.isConst());
  Assert (c2.isConst());
  Assert (utils::getSize(c1) == utils::getSize(c2));

  os << "(bv_disequal_constants " << utils::getSize(c1) << " ";

  std::ostringstream paren;

  for (int i = utils::getSize(c1) - 1; i >= 0; --i) {
    os << "(bvc ";
    os << (utils::getBit(c1, i) ? "b1" : "b0") << " ";
    paren << ")";
  }
  os << "bvn";
  os << paren.str();

  os << " ";

  for (int i = utils::getSize(c2) - 1; i >= 0; --i) {
    os << "(bvc ";
    os << (utils::getBit(c2, i) ? "b1" : "b0") << " ";

  }
  os << "bvn";
  os << paren.str();

  os << ")";
}

void LFSCBitVectorProof::printRewriteProof(std::ostream& os, const Node &n1, const Node &n2) {
  ProofLetMap emptyMap;
  os << "(rr_bv_default ";
  d_proofEngine->printBoundTerm(n2.toExpr(), os, emptyMap);
  os << " ";
  d_proofEngine->printBoundTerm(n1.toExpr(), os, emptyMap);
  os << ")";
}

} /* namespace CVC4 */
