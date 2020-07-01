/*********************                                                        */
/*! \file bitvector_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Guy Katz, Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** Contains implementions (e.g. code for printing bitblasting bindings that is
 ** common to all kinds of bitvector proofs.
 **/

#include "proof/bitvector_proof.h"
#include "options/bv_options.h"
#include "options/proof_options.h"
#include "proof/proof_output_channel.h"
#include "proof/theory_proof.h"
#include "prop/sat_solver_types.h"
#include "theory/bv/bitblast/bitblaster.h"
#include "theory/bv/theory_bv.h"

namespace CVC4 {

namespace proof {
BitVectorProof::BitVectorProof(theory::bv::TheoryBV* bv,
                               TheoryProofEngine* proofEngine)
    : TheoryProof(bv, proofEngine),
      d_declarations(),
      d_seenBBTerms(),
      d_bbTerms(),
      d_bbAtoms(),
      d_bitblaster(nullptr),
      d_useConstantLetification(false),
      d_cnfProof()
{
}

void BitVectorProof::setBitblaster(theory::bv::TBitblaster<Node>* bb)
{
  Assert(d_bitblaster == NULL);
  d_bitblaster = bb;
}

void BitVectorProof::registerTermBB(Expr term)
{
  Debug("pf::bv") << "BitVectorProof::registerTermBB( " << term
                  << " )" << std::endl;

  if (d_seenBBTerms.find(term) != d_seenBBTerms.end()) return;

  d_seenBBTerms.insert(term);
  d_bbTerms.push_back(term);

  // If this term gets used in the final proof, we will want to register it.
  // However, we don't know this at this point; and when the theory proof engine
  // sees it, if it belongs to another theory, it won't register it with this
  // proof. So, we need to tell the engine to inform us.

  if (theory::Theory::theoryOf(term) != theory::THEORY_BV)
  {
    Debug("pf::bv") << "\tMarking term " << term
                    << " for future BV registration" << std::endl;
    d_proofEngine->markTermForFutureRegistration(term, theory::THEORY_BV);
  }
}

void BitVectorProof::registerAtomBB(Expr atom, Expr atom_bb) {
  Debug("pf::bv") << "BitVectorProof::registerAtomBB( " << atom
                  << ", " << atom_bb << " )" << std::endl;

  Expr def = atom.eqExpr(atom_bb);
  d_bbAtoms.insert(std::make_pair(atom, def));
  registerTerm(atom);

  // Register the atom's terms for bitblasting
  registerTermBB(atom[0]);
  registerTermBB(atom[1]);
}

void BitVectorProof::registerTerm(Expr term) {
  Debug("pf::bv") << "BitVectorProof::registerTerm( " << term << " )"
                  << std::endl;

  if (options::lfscLetification() && term.isConst()
      && term.getType().isBitVector())
  {
    if (d_constantLetMap.find(term) == d_constantLetMap.end()) {
      std::ostringstream name;
      name << "letBvc" << d_constantLetMap.size();
      d_constantLetMap[term] = name.str();
    }
  }

  d_usedBB.insert(term);

  if (theory::Theory::isLeafOf(term, theory::THEORY_BV) && !term.isConst())
  {
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

std::string BitVectorProof::getBBTermName(Expr expr)
{
  Debug("pf::bv") << "BitVectorProof::getBBTermName( " << expr << " ) = bt"
                  << expr.getId() << std::endl;
  std::ostringstream os;
  os << "bt" << expr.getId();
  return os.str();
}

void BitVectorProof::printOwnedTermAsType(Expr term,
                                          std::ostream& os,
                                          const ProofLetMap& map,
                                          TypeNode expectedType)
{
  Debug("pf::bv") << std::endl
                  << "(pf::bv) BitVectorProof::printOwnedTerm( " << term
                  << " ), theory is: " << theory::Theory::theoryOf(term)
                  << std::endl;

  Assert(theory::Theory::theoryOf(term) == theory::THEORY_BV);

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

void BitVectorProof::printEmptyClauseProof(std::ostream& os,
                                           std::ostream& paren)
{
  Assert(options::bitblastMode() == options::BitblastMode::EAGER)
      << "the BV theory should only be proving bottom directly in the eager "
         "bitblasting mode";
}

void BitVectorProof::printBitOf(Expr term,
                                std::ostream& os,
                                const ProofLetMap& map)
{
  Assert(term.getKind() == kind::BITVECTOR_BITOF);
  unsigned bit = term.getOperator().getConst<BitVectorBitOf>().d_bitIndex;
  Expr var = term[0];

  Debug("pf::bv") << "BitVectorProof::printBitOf( " << term << " ), "
                  << "bit = " << bit << ", var = " << var << std::endl;

  os << "(bitof ";
  os << d_exprToVariableName[var];
  os << " " << bit << ")";
}

void BitVectorProof::printConstant(Expr term, std::ostream& os)
{
  Assert(term.isConst());
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

void BitVectorProof::printOperatorNary(Expr term,
                                       std::ostream& os,
                                       const ProofLetMap& map)
{
  std::string op = utils::toLFSCKindTerm(term);
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

void BitVectorProof::printOperatorUnary(Expr term,
                                        std::ostream& os,
                                        const ProofLetMap& map)
{
  os <<"(";
  os << utils::toLFSCKindTerm(term) << " " << utils::getSize(term) <<" ";
  os << " ";
  d_proofEngine->printBoundTerm(term[0], os, map);
  os <<")";
}

void BitVectorProof::printPredicate(Expr term,
                                    std::ostream& os,
                                    const ProofLetMap& map)
{
  os <<"(";
  os << utils::toLFSCKindTerm(term) << " " << utils::getSize(term[0]) <<" ";
  os << " ";
  d_proofEngine->printBoundTerm(term[0], os, map);
  os << " ";
  d_proofEngine->printBoundTerm(term[1], os, map);
  os <<")";
}

void BitVectorProof::printOperatorParametric(Expr term,
                                             std::ostream& os,
                                             const ProofLetMap& map)
{
  os <<"(";
  os << utils::toLFSCKindTerm(term) << " " << utils::getSize(term) <<" ";
  os <<" ";
  if (term.getKind() == kind::BITVECTOR_REPEAT) {
    unsigned amount =
        term.getOperator().getConst<BitVectorRepeat>().d_repeatAmount;
    os << amount <<" _ ";
  }
  if (term.getKind() == kind::BITVECTOR_SIGN_EXTEND) {
    unsigned amount =
        term.getOperator().getConst<BitVectorSignExtend>().d_signExtendAmount;
    os << amount <<" _ ";
  }

  if (term.getKind() == kind::BITVECTOR_ZERO_EXTEND) {
    unsigned amount =
        term.getOperator().getConst<BitVectorZeroExtend>().d_zeroExtendAmount;
    os << amount<<" _ ";
  }
  if (term.getKind() == kind::BITVECTOR_EXTRACT) {
    unsigned low = utils::getExtractLow(term);
    unsigned high = utils::getExtractHigh(term);
    os << high <<" " << low << " " << utils::getSize(term[0]);
  }
  os <<" ";
  Assert(term.getNumChildren() == 1);
  d_proofEngine->printBoundTerm(term[0], os, map);
  os <<")";
}

void BitVectorProof::printOwnedSort(Type type, std::ostream& os)
{
  Debug("pf::bv") << std::endl
                  << "(pf::bv) BitVectorProof::printOwnedSort( " << type << " )"
                  << std::endl;
  Assert(type.isBitVector());
  unsigned width = utils::getSize(type);
  os << "(BitVec " << width << ")";
}

void BitVectorProof::printSortDeclarations(std::ostream& os,
                                           std::ostream& paren)
{
  // Nothing to do here at this point.
}

void BitVectorProof::printTermDeclarations(std::ostream& os,
                                           std::ostream& paren)
{
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

void BitVectorProof::printDeferredDeclarations(std::ostream& os,
                                               std::ostream& paren)
{
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

void BitVectorProof::printAliasingDeclarations(std::ostream& os,
                                               std::ostream& paren,
                                               const ProofLetMap& globalLetMap)
{
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

void BitVectorProof::printTermBitblasting(Expr term, std::ostream& os)
{
  // TODO: once we have the operator elimination rules remove those that we
  // eliminated
  Assert(term.getType().isBitVector());
  Kind kind = term.getKind();

  if (theory::Theory::isLeafOf(term, theory::THEORY_BV) && !term.isConst())
  {
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
      unsigned amount =
          term.getOperator().getConst<BitVectorRepeat>().d_repeatAmount;
      os << amount;
    }
    if (term.getKind() == kind::BITVECTOR_SIGN_EXTEND) {
      unsigned amount =
          term.getOperator().getConst<BitVectorSignExtend>().d_signExtendAmount;
      os << amount;
    }

    if (term.getKind() == kind::BITVECTOR_ZERO_EXTEND) {
      unsigned amount =
          term.getOperator().getConst<BitVectorZeroExtend>().d_zeroExtendAmount;
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

  default: Unreachable() << "BitVectorProof Unknown operator";
  }
}

void BitVectorProof::printAtomBitblasting(Expr atom,
                                          std::ostream& os,
                                          bool swap)
{
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

    os << "(bv_bbl_" << utils::toLFSCKindTerm(atom);

    if (swap) {os << "_swap";}

    os << " _ _ _ _ _ _ ";
    os << getBBTermName(atom[0]);
    os << " ";
    os << getBBTermName(atom[1]);
    os << ")";

    return;
  }
  default: Unreachable() << "BitVectorProof Unknown atom kind";
  }
}

void BitVectorProof::printAtomBitblastingToFalse(Expr atom, std::ostream& os)
{
  Assert(atom.getKind() == kind::EQUAL);

  os << "(bv_bbl_=_false";
  os << " _ _ _ _ _ _ ";
  os << getBBTermName(atom[0]);

  os << " ";

  os << getBBTermName(atom[1]);

  os << ")";
}

void BitVectorProof::printBitblasting(std::ostream& os, std::ostream& paren)
{
  // bit-blast terms
  {
    Debug("pf::bv")
        << "BitVectorProof::printBitblasting: the bitblasted terms are: "
        << std::endl;
    std::vector<Expr>::const_iterator it = d_bbTerms.begin();
    std::vector<Expr>::const_iterator end = d_bbTerms.end();

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
    if (d_usedBB.find(*it) == d_usedBB.end()
        && options::bitblastMode() != options::BitblastMode::EAGER)
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
    if (d_usedBB.find(ait->first) == d_usedBB.end()
        && options::bitblastMode() != options::BitblastMode::EAGER)
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

theory::TheoryId BitVectorProof::getTheoryId() { return theory::THEORY_BV; }

const std::set<Node>* BitVectorProof::getAtomsInBitblastingProof()
{
  return &d_atomsInBitblastingProof;
}

std::string BitVectorProof::assignAlias(Expr expr)
{
  Assert(d_exprToVariableName.find(expr) == d_exprToVariableName.end());

  std::stringstream ss;
  ss << "fbv" << d_assignedAliases.size();
  Debug("pf::bv") << "assignAlias( " << expr << ") = " << ss.str() << std::endl;
  d_assignedAliases[expr] = ss.str();
  return ss.str();
}

bool BitVectorProof::hasAlias(Expr expr)
{
  return d_assignedAliases.find(expr) != d_assignedAliases.end();
}

void BitVectorProof::printConstantDisequalityProof(
    std::ostream& os, Expr c1, Expr c2, const ProofLetMap& globalLetMap)
{
  Assert(c1.isConst());
  Assert(c2.isConst());
  Assert(utils::getSize(c1) == utils::getSize(c2));

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

void BitVectorProof::printRewriteProof(std::ostream& os,
                                       const Node& n1,
                                       const Node& n2)
{
  ProofLetMap emptyMap;
  os << "(rr_bv_default ";
  d_proofEngine->printBoundTerm(n2.toExpr(), os, emptyMap);
  os << " ";
  d_proofEngine->printBoundTerm(n1.toExpr(), os, emptyMap);
  os << ")";
}

}  // namespace proof

}  // namespace CVC4
