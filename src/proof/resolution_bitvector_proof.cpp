/*********************                                                        */
/*! \file resolution_bitvector_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir, Liana Hadarean, Guy Katz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]

 ** \todo document this file

**/

#include "proof/resolution_bitvector_proof.h"
#include "options/bv_options.h"
#include "options/proof_options.h"
#include "proof/array_proof.h"
#include "proof/bitvector_proof.h"
#include "proof/clause_id.h"
#include "proof/lfsc_proof_printer.h"
#include "proof/proof_output_channel.h"
#include "proof/proof_utils.h"
#include "proof/sat_proof_implementation.h"
#include "prop/bvminisat/bvminisat.h"
#include "prop/sat_solver_types.h"
#include "theory/bv/bitblast/bitblaster.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_rewrite_rules.h"

#include <iostream>
#include <sstream>

using namespace CVC4::theory;
using namespace CVC4::theory::bv;

namespace CVC4 {

namespace proof {

ResolutionBitVectorProof::ResolutionBitVectorProof(
    theory::bv::TheoryBV* bv, TheoryProofEngine* proofEngine)
    : BitVectorProof(bv, proofEngine),
      d_resolutionProof(),
      d_isAssumptionConflict(false)
{
}

void ResolutionBitVectorProof::initSatProof(CVC4::BVMinisat::Solver* solver)
{
  Assert(d_resolutionProof == NULL);
  d_resolutionProof.reset(new BVSatProof(solver, &d_fakeContext, "bb", true));
}

void ResolutionBitVectorProof::initCnfProof(prop::CnfStream* cnfStream,
                                            context::Context* cnf,
                                            prop::SatVariable trueVar,
                                            prop::SatVariable falseVar)
{
  Assert(d_resolutionProof != NULL);
  Assert(d_cnfProof == nullptr);
  d_cnfProof.reset(new LFSCCnfProof(cnfStream, cnf, "bb"));

  d_cnfProof->registerTrueUnitClause(d_resolutionProof->getTrueUnit());
  d_cnfProof->registerFalseUnitClause(d_resolutionProof->getFalseUnit());
}

void ResolutionBitVectorProof::attachToSatSolver(prop::SatSolver& sat_solver)
{
  sat_solver.setResolutionProofLog(this);
}

BVSatProof* ResolutionBitVectorProof::getSatProof()
{
  Assert(d_resolutionProof != NULL);
  return d_resolutionProof.get();
}

void ResolutionBitVectorProof::startBVConflict(
    CVC4::BVMinisat::Solver::TCRef cr)
{
  d_resolutionProof->startResChain(cr);
}

void ResolutionBitVectorProof::startBVConflict(
    CVC4::BVMinisat::Solver::TLit lit)
{
  d_resolutionProof->startResChain(lit);
}

void ResolutionBitVectorProof::endBVConflict(
    const CVC4::BVMinisat::Solver::TLitVec& confl)
{
  Debug("pf::bv") << "ResolutionBitVectorProof::endBVConflict called"
                  << std::endl;

  std::vector<Expr> expr_confl;
  for (int i = 0; i < confl.size(); ++i)
  {
    prop::SatLiteral lit = prop::BVMinisatSatSolver::toSatLiteral(confl[i]);
    Expr atom = d_cnfProof->getAtom(lit.getSatVariable()).toExpr();
    Expr expr_lit = lit.isNegated() ? atom.notExpr() : atom;
    expr_confl.push_back(expr_lit);
  }

  Expr conflict = utils::mkSortedExpr(kind::OR, expr_confl);
  Debug("pf::bv") << "Make conflict for " << conflict << std::endl;

  if (d_bbConflictMap.find(conflict) != d_bbConflictMap.end())
  {
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
  Debug("pf::bv") << "ResolutionBitVectorProof::endBVConflict id" << clause_id
                  << " => " << conflict << "\n";
  d_isAssumptionConflict = false;
}

void ResolutionBitVectorProof::finalizeConflicts(std::vector<Expr>& conflicts)
{
  if (options::bitblastMode() == options::BitblastMode::EAGER)
  {
    Debug("pf::bv") << "Construct full proof." << std::endl;
    d_resolutionProof->constructProof();
    return;
  }

  for (unsigned i = 0; i < conflicts.size(); ++i)
  {
    Expr confl = conflicts[i];
    Debug("pf::bv") << "Finalize conflict #" << i << ": " << confl << std::endl;

    // Special case: if the conflict has a (true) or a (not false) in it, it is
    // trivial...
    bool ignoreConflict = false;
    if ((confl.isConst() && confl.getConst<bool>())
        || (confl.getKind() == kind::NOT && confl[0].isConst()
            && !confl[0].getConst<bool>()))
    {
      ignoreConflict = true;
    }
    else if (confl.getKind() == kind::OR)
    {
      for (unsigned k = 0; k < confl.getNumChildren(); ++k)
      {
        if ((confl[k].isConst() && confl[k].getConst<bool>())
            || (confl[k].getKind() == kind::NOT && confl[k][0].isConst()
                && !confl[k][0].getConst<bool>()))
        {
          ignoreConflict = true;
        }
      }
    }
    if (ignoreConflict)
    {
      Debug("pf::bv") << "Ignoring conflict due to (true) or (not false)"
                      << std::endl;
      continue;
    }

    if (d_bbConflictMap.find(confl) != d_bbConflictMap.end())
    {
      ClauseId id = d_bbConflictMap[confl];
      d_resolutionProof->collectClauses(id);
    }
    else
    {
      // There is no exact match for our conflict, but maybe it is a subset of
      // another conflict
      ExprToClauseId::const_iterator it;
      bool matchFound = false;
      for (it = d_bbConflictMap.begin(); it != d_bbConflictMap.end(); ++it)
      {
        Expr possibleMatch = it->first;
        if (possibleMatch.getKind() != kind::OR)
        {
          // This is a single-node conflict. If this node is in the conflict
          // we're trying to prove, we have a match.
          for (unsigned k = 0; k < confl.getNumChildren(); ++k)
          {
            if (confl[k] == possibleMatch)
            {
              matchFound = true;
              d_resolutionProof->collectClauses(it->second);
              break;
            }
          }
        }
        else
        {
          if (possibleMatch.getNumChildren() > confl.getNumChildren()) continue;

          unsigned k = 0;
          bool matching = true;
          for (unsigned j = 0; j < possibleMatch.getNumChildren(); ++j)
          {
            // j is the index in possibleMatch
            // k is the index in confl
            while (k < confl.getNumChildren() && confl[k] != possibleMatch[j])
            {
              ++k;
            }
            if (k == confl.getNumChildren())
            {
              // We couldn't find a match for possibleMatch[j], so not a match
              matching = false;
              break;
            }
          }

          if (matching)
          {
            Debug("pf::bv")
                << "Collecting info from a sub-conflict" << std::endl;
            d_resolutionProof->collectClauses(it->second);
            matchFound = true;
            break;
          }
        }
      }

      if (!matchFound)
      {
        Debug("pf::bv") << "Do not collect clauses for " << confl << std::endl
                        << "Dumping existing conflicts:" << std::endl;

        i = 0;
        for (it = d_bbConflictMap.begin(); it != d_bbConflictMap.end(); ++it)
        {
          ++i;
          Debug("pf::bv") << "\tConflict #" << i << ": " << it->first
                          << std::endl;
        }

        Unreachable();
      }
    }
  }
}

void LfscResolutionBitVectorProof::printTheoryLemmaProof(
    std::vector<Expr>& lemma,
    std::ostream& os,
    std::ostream& paren,
    const ProofLetMap& map)
{
  Debug("pf::bv")
      << "(pf::bv) LfscResolutionBitVectorProof::printTheoryLemmaProof called"
      << std::endl;
  Expr conflict = utils::mkSortedExpr(kind::OR, lemma);
  Debug("pf::bv") << "\tconflict = " << conflict << std::endl;

  if (d_bbConflictMap.find(conflict) != d_bbConflictMap.end())
  {
    std::ostringstream lemma_paren;
    for (unsigned i = 0; i < lemma.size(); ++i)
    {
      Expr lit = lemma[i];

      if (lit.getKind() == kind::NOT)
      {
        os << "(intro_assump_t _ _ _ ";
      }
      else
      {
        os << "(intro_assump_f _ _ _ ";
      }
      lemma_paren << ")";
      // print corresponding literal in main sat solver
      ProofManager* pm = ProofManager::currentPM();
      CnfProof* cnf = pm->getCnfProof();
      prop::SatLiteral main_lit = cnf->getLiteral(lit);
      os << pm->getLitName(main_lit);
      os << " ";
      // print corresponding literal in bv sat solver
      prop::SatVariable bb_var = d_cnfProof->getLiteral(lit).getSatVariable();
      os << pm->getAtomName(bb_var, "bb");
      os << "(\\ unit" << bb_var << "\n";
      lemma_paren << ")";
    }
    Expr lem = utils::mkOr(lemma);
    Assert(d_bbConflictMap.find(lem) != d_bbConflictMap.end());
    ClauseId lemma_id = d_bbConflictMap[lem];
    proof::LFSCProofPrinter::printAssumptionsResolution(
        d_resolutionProof.get(), lemma_id, os, lemma_paren);
    os << lemma_paren.str();
  }
  else
  {
    Debug("pf::bv") << "Found a non-recorded conflict. Looking for a matching "
                       "sub-conflict..."
                    << std::endl;

    bool matching;

    ExprToClauseId::const_iterator it;
    unsigned i = 0;
    for (it = d_bbConflictMap.begin(); it != d_bbConflictMap.end(); ++it)
    {
      // Our conflict is sorted, and the records are also sorted.
      ++i;
      Expr possibleMatch = it->first;

      if (possibleMatch.getKind() != kind::OR)
      {
        // This is a single-node conflict. If this node is in the conflict we're
        // trying to prove, we have a match.
        matching = false;

        for (unsigned k = 0; k < conflict.getNumChildren(); ++k)
        {
          if (conflict[k] == possibleMatch)
          {
            matching = true;
            break;
          }
        }
      }
      else
      {
        if (possibleMatch.getNumChildren() > conflict.getNumChildren())
          continue;

        unsigned k = 0;

        matching = true;
        for (unsigned j = 0; j < possibleMatch.getNumChildren(); ++j)
        {
          // j is the index in possibleMatch
          // k is the index in conflict
          while (k < conflict.getNumChildren()
                 && conflict[k] != possibleMatch[j])
          {
            ++k;
          }
          if (k == conflict.getNumChildren())
          {
            // We couldn't find a match for possibleMatch[j], so not a match
            matching = false;
            break;
          }
        }
      }

      if (matching)
      {
        Debug("pf::bv") << "Found a match with conflict #" << i << ": "
                        << std::endl
                        << possibleMatch << std::endl;
        // The rest is just a copy of the usual handling, if a precise match is
        // found. We only use the literals that appear in the matching conflict,
        // though, and not in the original lemma - as these may not have even
        // been bit blasted!
        std::ostringstream lemma_paren;

        if (possibleMatch.getKind() == kind::OR)
        {
          for (const Expr& lit : possibleMatch)
          {
            if (lit.getKind() == kind::NOT)
            {
              os << "(intro_assump_t _ _ _ ";
            }
            else
            {
              os << "(intro_assump_f _ _ _ ";
            }
            lemma_paren << ")";
            // print corresponding literal in main sat solver
            ProofManager* pm = ProofManager::currentPM();
            CnfProof* cnf = pm->getCnfProof();
            prop::SatLiteral main_lit = cnf->getLiteral(lit);
            os << pm->getLitName(main_lit);
            os << " ";
            // print corresponding literal in bv sat solver
            prop::SatVariable bb_var =
                d_cnfProof->getLiteral(lit).getSatVariable();
            os << pm->getAtomName(bb_var, "bb");
            os << "(\\ unit" << bb_var << "\n";
            lemma_paren << ")";
          }
        }
        else
        {
          // The conflict only consists of one node, either positive or
          // negative.
          Expr lit = possibleMatch;
          if (lit.getKind() == kind::NOT)
          {
            os << "(intro_assump_t _ _ _ ";
          }
          else
          {
            os << "(intro_assump_f _ _ _ ";
          }
          lemma_paren << ")";
          // print corresponding literal in main sat solver
          ProofManager* pm = ProofManager::currentPM();
          CnfProof* cnf = pm->getCnfProof();
          prop::SatLiteral main_lit = cnf->getLiteral(lit);
          os << pm->getLitName(main_lit);
          os << " ";
          // print corresponding literal in bv sat solver
          prop::SatVariable bb_var =
              d_cnfProof->getLiteral(lit).getSatVariable();
          os << pm->getAtomName(bb_var, "bb");
          os << "(\\ unit" << bb_var << "\n";
          lemma_paren << ")";
        }

        ClauseId lemma_id = it->second;
        proof::LFSCProofPrinter::printAssumptionsResolution(
            d_resolutionProof.get(), lemma_id, os, lemma_paren);
        os << lemma_paren.str();

        return;
      }
    }

    // We failed to find a matching sub conflict. The last hope is that the
    // conflict has a FALSE assertion in it; this can happen in some corner
    // cases, where the FALSE is the result of a rewrite.

    for (const Expr& lit : lemma)
    {
      if (lit.getKind() == kind::NOT && lit[0] == utils::mkFalse())
      {
        Debug("pf::bv") << "Lemma has a (not false) literal" << std::endl;
        os << "(clausify_false ";
        os << ProofManager::getLitName(lit);
        os << ")";
        return;
      }
    }

    Debug("pf::bv") << "Failed to find a matching sub-conflict..." << std::endl
                    << "Dumping existing conflicts:" << std::endl;

    i = 0;
    for (it = d_bbConflictMap.begin(); it != d_bbConflictMap.end(); ++it)
    {
      ++i;
      Debug("pf::bv") << "\tConflict #" << i << ": " << it->first << std::endl;
    }

    Unreachable();
  }
}

void LfscResolutionBitVectorProof::calculateAtomsInBitblastingProof()
{
  // Collect the input clauses used
  IdToSatClause used_lemmas;
  IdToSatClause used_inputs;
  d_resolutionProof->collectClausesUsed(used_inputs, used_lemmas);
  d_cnfProof->collectAtomsForClauses(used_inputs, d_atomsInBitblastingProof);
  Assert(used_lemmas.empty());
}

void LfscResolutionBitVectorProof::printBBDeclarationAndCnf(std::ostream& os,
                                                            std::ostream& paren,
                                                            ProofLetMap& letMap)
{
  // print mapping between theory atoms and internal SAT variables
  os << std::endl << ";; BB atom mapping\n" << std::endl;

  std::set<Node>::iterator atomIt;
  Debug("pf::bv") << std::endl
                  << "BV Dumping atoms from inputs: " << std::endl
                  << std::endl;
  for (atomIt = d_atomsInBitblastingProof.begin();
       atomIt != d_atomsInBitblastingProof.end();
       ++atomIt)
  {
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
       it != used_inputs.end();
       ++it)
  {
    d_cnfProof->printCnfProofForClause(it->first, it->second, os, paren);
  }

  os << std::endl << " ;; Bit-blasting learned clauses \n" << std::endl;
  proof::LFSCProofPrinter::printResolutions(d_resolutionProof.get(), os, paren);
}

void LfscResolutionBitVectorProof::printEmptyClauseProof(std::ostream& os,
                                                         std::ostream& paren)
{
  Assert(options::bitblastMode() == options::BitblastMode::EAGER)
      << "the BV theory should only be proving bottom directly in the eager "
         "bitblasting mode";
  proof::LFSCProofPrinter::printResolutionEmptyClause(
      d_resolutionProof.get(), os, paren);
}

}  // namespace proof

} /* namespace CVC4 */
