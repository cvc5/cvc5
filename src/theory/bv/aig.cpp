/*********************                                                        */
/*! \file aig.cpp
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none.
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/bv/bitblaster.h"
#include "theory/bv/aig.h"
#include "theory/rewriter.h"
#include "prop/bvminisat/bvminisat.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv; 
using namespace std;


AigBitblaster::AigBitblaster(AigSimplifier* aigSimplifier)
  : d_aigSimplifer(aigSimplifier)
{}

AigBitblaster::~AigBitblaster() {}

void AigBitblaster::storeVariable(TNode var) {
  for (unsigned i = 0; i < utils::getSize(var); ++i) {
    Node bit_i = utils::mkBitOf(var, i);
    d_aigSimplifer->mkInput(bit_i); 
  }
}

void AigBitblaster::bbFormula(TNode node) {
  Assert (node.getType().isBoolean());

  switch (node.getKind()) {
  case kind::AND:
  case kind::OR:
  case kind::IFF:
  case kind::XOR:
  case kind::IMPLIES:
    bbFormula(node[0]);
    bbFormula(node[1]); 
    break;
  case kind::ITE:
    bbFormula(node[0]);
    bbFormula(node[1]);
    bbFormula(node[2]); 
    break;
  case kind::NOT:
    bbFormula(node[0]); 
    break;
  case kind::CONST_BOOLEAN:
    break;
  default:
    bbAtom(node); 
  }
}

void AigBitblaster::bbAtom(TNode node) {
  if (hasBBAtom(node)) {
    return;
  }

  Debug("bitvector-bitblast") << "Bitblasting node " << node <<"\n";

  // the bitblasted definition of the atom
  Node normalized = Rewriter::rewrite(node);
  Node atom_bb = normalized.getKind() != kind::CONST_BOOLEAN ?
      Rewriter::rewrite(d_atomBBStrategies[normalized.getKind()](normalized, this)) :
      normalized;

  // converting the atom to Aig
  d_aigSimplifer->convertToAig(atom_bb);
  storeBBAtom(node);
}

void AigBitblaster::bbTerm(TNode node, Bits& bits) {
  if (hasBBTerm(node)) {
    getBBTerm(node, bits);
    return;
  }

  Debug("bitvector-bitblast") << "Bitblasting node " << node <<"\n";
  d_termBBStrategies[node.getKind()] (node, bits, this);

  Assert (bits.size() == utils::getSize(node));
  storeBBTerm(node, bits);
}



AigSimplifier::AigSimplifier(prop::BVSatSolverInterface* solver)
  : d_satSolver(solver)
  , d_asserted(false)
  , d_aigCache()
  , d_nodeToAigInput()
    //  , d_aigInputToNode()
  , d_aigOutput(NULL)
{

  Abc_Start();
  d_abcAigNetwork = Abc_NtkAlloc( ABC_NTK_STRASH, ABC_FUNC_AIG, 1); 
  char* pName("CVC4::theory::bv::AigNetwork");
  d_abcAigNetwork->pName = Extra_UtilStrsav(pName);
  d_trueAigNode = Abc_AigConst1(d_abcAigNetwork);
  d_falseAigNode = Abc_ObjNot(d_trueAigNode); 
  delete pName; 
}

AigSimplifier::~AigSimplifier() {
  Abc_Stop();
  delete d_abcAigNetwork;
}

Abc_Obj_t* AigSimplifier::convertToAig(TNode node) {
  if (hasAig(node))
    return getAig(node);

  Abc_Aig_t* man = (Abc_Aig_t*)d_abcAigNetwork->pManFunc;
  Abc_Obj_t* result; 
  switch (node.getKind()) {
  case kind::AND:
    {
      Abc_Obj_t* result = convertToAig(node[0]);
      for (unsigned i = 1; i < node.getNumChildren(); ++i) {
        Abc_Obj_t* child = convertToAig(node[i]);
        result = Abc_AigAnd(man, result, child);
      }
      break;
    }
  case kind::OR:
    {
      Abc_Obj_t* result = convertToAig(node[0]);
      for (unsigned i = 1; i < node.getNumChildren(); ++i) {
        Abc_Obj_t* child = convertToAig(node[i]);
        result = Abc_AigOr(man, result, child);
      }
      break;
    }
  case kind::IFF:
    {
      Assert (node.getNumChildren() == 2); 
      Abc_Obj_t* child1 = convertToAig(node[0]);
      Abc_Obj_t* child2 = convertToAig(node[1]);

      // bit-blasting as ~(child1 xor child2)
      Abc_Obj_t* different = Abc_AigXor(man, child1, child2);
      result = Abc_ObjNot(different);
      break;
    }
  case kind::XOR:
    {
      Abc_Obj_t* result = convertToAig(node[0]);
      for (unsigned i = 1; i < node.getNumChildren(); ++i) {
        Abc_Obj_t* child = convertToAig(node[i]);
        result = Abc_AigXor(man, result, child);
      }
      break;
    }
  case kind::IMPLIES:
    {
      Assert (node.getNumChildren() == 2); 
      Abc_Obj_t* child1 = convertToAig(node[0]);
      Abc_Obj_t* child2 = convertToAig(node[1]);
      Abc_Obj_t* not_child2 = Abc_ObjNot(child2);
      result = Abc_AigOr(man, child1, not_child2);
      break;
    }
  case kind::ITE:
    {
      Assert (node.getNumChildren() == 3); 
      Abc_Obj_t* a = convertToAig(node[0]);
      Abc_Obj_t* b = convertToAig(node[1]);
      Abc_Obj_t* c = convertToAig(node[2]);
      result = Abc_AigMux(man, a, b, c); 
      break;
    }
  case kind::NOT:
    {
      Abc_Obj_t* child1 = convertToAig(node[0]);
      result = Abc_ObjNot(child1);
      break;
    }
  case kind::CONST_BOOLEAN:
    {
      result = node.getConst<bool>() ? d_trueAigNode : d_falseAigNode; 
      break;
    }
  default:
    Unreachable("Can't convert to AIG."); 
  }

  cacheAig(node, result);
  return result; 
}

void AigSimplifier::cacheAig(TNode node, Abc_Obj_t* aig) {
  Assert (!hasAig(node));
  d_aigCache.insert(make_pair(node, aig));
}
bool AigSimplifier::hasAig(TNode node) {
  return d_aigCache.find(node) != d_aigCache.end(); 
}
Abc_Obj_t* AigSimplifier::getAig(TNode node) {
  Assert(hasAig(node));
  return d_aigCache.find(node)->second; 
}

void AigSimplifier::mkInput(TNode input) {
  Assert (!hasInput(input));
  Assert(input.getKind() == kind::BITVECTOR_BITOF ||
         (input.getType().isBoolean() &&
          input.getKind() == kind::VARIABLE));
  Abc_Obj_t* aig_input = Abc_NtkCreatePi(d_abcAigNetwork);
  d_aigCache.insert(make_pair(input, aig_input));
  d_nodeToAigInput.insert(make_pair(input, aig_input));
  // d_aigInputToNode.insert(make_pair(aig_input, input)); 
}

bool AigSimplifier::hasInput(TNode input) {
  return d_nodeToAigInput.find(input) != d_nodeToAigInput.end(); 
}

void AigSimplifier::simplifyAig() {
  Assert (!d_asserted);
  Abc_AigCleanup((Abc_Aig_t*)d_abcAigNetwork->pManFunc);
  Assert (Abc_NtkCheck(d_abcAigNetwork));
  
  // run simplifications
  // dump to cnf
  
  d_asserted = true; 
}

void AigSimplifier::convertToCnfAndAssert() {
  // TODO convert to cnf and assert to current sat solver
}

bool AigSimplifier::solve() {
  return d_satSolver->solve(); 
}

void AigSimplifier::setOutput(TNode query) {
  Assert(d_aigOutput == NULL); 
  Abc_Obj_t* aig_query = convertToAig(query);
  d_aigOutput = Abc_NtkCreatePo(d_abcAigNetwork); 
  Abc_ObjAddFanin(d_aigOutput, aig_query); 
}

