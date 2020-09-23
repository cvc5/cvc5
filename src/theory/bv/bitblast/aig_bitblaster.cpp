/*********************                                                        */
/*! \file aig_bitblaster.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief AIG bitblaster.
 **
 ** AIG bitblaster.
 **/

#include "theory/bv/bitblast/aig_bitblaster.h"

#include "base/check.h"
#include "cvc4_private.h"
#include "options/bv_options.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver_factory.h"
#include "smt/smt_statistics_registry.h"

#ifdef CVC4_USE_ABC

extern "C" {
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "sat/cnf/cnf.h"

extern Aig_Man_t* Abc_NtkToDar(Abc_Ntk_t* pNtk, int fExors, int fRegisters);
}

// Function is defined as static in ABC. Not sure how else to do this.
static inline int Cnf_Lit2Var(int Lit)
{
  return (Lit & 1) ? -(Lit >> 1) - 1 : (Lit >> 1) + 1;
}

namespace CVC4 {
namespace theory {
namespace bv {

template <> inline
std::string toString<Abc_Obj_t*> (const std::vector<Abc_Obj_t*>& bits) {
  Unreachable() << "Don't know how to print AIG";
} 


template <> inline
Abc_Obj_t* mkTrue<Abc_Obj_t*>() {
  return Abc_AigConst1(AigBitblaster::currentAigNtk());  
}

template <> inline
Abc_Obj_t* mkFalse<Abc_Obj_t*>() {
  return Abc_ObjNot(mkTrue<Abc_Obj_t*>()); 
}

template <> inline
Abc_Obj_t* mkNot<Abc_Obj_t*>(Abc_Obj_t* a) {
  return Abc_ObjNot(a); 
}

template <> inline
Abc_Obj_t* mkOr<Abc_Obj_t*>(Abc_Obj_t* a, Abc_Obj_t* b) {
  return Abc_AigOr(AigBitblaster::currentAigM(), a, b); 
}

template <> inline
Abc_Obj_t* mkOr<Abc_Obj_t*>(const std::vector<Abc_Obj_t*>& children) {
  Assert(children.size());
  if (children.size() == 1)
    return children[0];
  
  Abc_Obj_t* result = children[0];
  for (unsigned i = 1; i < children.size(); ++i) {
    result = Abc_AigOr(AigBitblaster::currentAigM(), result, children[i]); 
  }
  return result;
}


template <> inline
Abc_Obj_t* mkAnd<Abc_Obj_t*>(Abc_Obj_t* a, Abc_Obj_t* b) {
  return Abc_AigAnd(AigBitblaster::currentAigM(), a, b); 
}

template <> inline
Abc_Obj_t* mkAnd<Abc_Obj_t*>(const std::vector<Abc_Obj_t*>& children) {
  Assert(children.size());
  if (children.size() == 1)
    return children[0];
  
  Abc_Obj_t* result = children[0];
  for (unsigned i = 1; i < children.size(); ++i) {
    result = Abc_AigAnd(AigBitblaster::currentAigM(), result, children[i]); 
  }
  return result;
}

template <> inline
Abc_Obj_t* mkXor<Abc_Obj_t*>(Abc_Obj_t* a, Abc_Obj_t* b) {
  return Abc_AigXor(AigBitblaster::currentAigM(), a, b); 
}

template <> inline
Abc_Obj_t* mkIff<Abc_Obj_t*>(Abc_Obj_t* a, Abc_Obj_t* b) {
  return mkNot(mkXor(a, b)); 
}

template <> inline
Abc_Obj_t* mkIte<Abc_Obj_t*>(Abc_Obj_t* cond, Abc_Obj_t* a, Abc_Obj_t* b) {
  return Abc_AigMux(AigBitblaster::currentAigM(), cond, a, b); 
}

thread_local Abc_Ntk_t* AigBitblaster::s_abcAigNetwork = nullptr;

Abc_Ntk_t* AigBitblaster::currentAigNtk() {
  if (!AigBitblaster::s_abcAigNetwork) {
    Abc_Start();
    s_abcAigNetwork = Abc_NtkAlloc( ABC_NTK_STRASH, ABC_FUNC_AIG, 1);
    char pName[] = "CVC4::theory::bv::AigNetwork";
    s_abcAigNetwork->pName = Extra_UtilStrsav(pName);
  }
  
  return s_abcAigNetwork;
}


Abc_Aig_t* AigBitblaster::currentAigM() {
  return (Abc_Aig_t*)(currentAigNtk()->pManFunc);
}

AigBitblaster::AigBitblaster()
    : TBitblaster<Abc_Obj_t*>(),
      d_nullContext(new context::Context()),
      d_aigCache(),
      d_bbAtoms(),
      d_aigOutputNode(NULL),
      d_notify()
{
  prop::SatSolver* solver = nullptr;
  switch (options::bvSatSolver())
  {
    case options::SatSolverMode::MINISAT:
    {
      prop::BVSatSolverInterface* minisat =
          prop::SatSolverFactory::createMinisat(
              d_nullContext.get(), smtStatisticsRegistry(), "AigBitblaster");
      d_notify.reset(new MinisatEmptyNotify());
      minisat->setNotify(d_notify.get());
      solver = minisat;
      break;
    }
    case options::SatSolverMode::CADICAL:
      solver = prop::SatSolverFactory::createCadical(smtStatisticsRegistry(),
                                                     "AigBitblaster");
      break;
    case options::SatSolverMode::CRYPTOMINISAT:
      solver = prop::SatSolverFactory::createCryptoMinisat(
          smtStatisticsRegistry(), "AigBitblaster");
      break;
    case options::SatSolverMode::KISSAT:
      solver = prop::SatSolverFactory::createKissat(smtStatisticsRegistry(),
                                                    "AigBitblaster");
      break;
    default: CVC4_FATAL() << "Unknown SAT solver type";
  }
  d_satSolver.reset(solver);
}

AigBitblaster::~AigBitblaster() {}

Abc_Obj_t* AigBitblaster::bbFormula(TNode node) {
  Assert(node.getType().isBoolean());
  Debug("bitvector-bitblast") << "AigBitblaster::bbFormula "<< node << "\n"; 
  
  if (hasAig(node))
    return getAig(node);
  
  Abc_Obj_t* result = NULL;
  
  Debug("bitvector-aig") << "AigBitblaster::convertToAig " << node <<"\n"; 
  switch (node.getKind()) {
  case kind::AND:
    {
      result = bbFormula(node[0]);
      for (unsigned i = 1; i < node.getNumChildren(); ++i) {
        Abc_Obj_t* child = bbFormula(node[i]);
        result = mkAnd(result, child);
      }
      break;
    }
  case kind::OR:
    {
      result = bbFormula(node[0]);
      for (unsigned i = 1; i < node.getNumChildren(); ++i) {
        Abc_Obj_t* child = bbFormula(node[i]);
        result = mkOr(result, child);
      }
      break;
    }
  case kind::XOR:
    {
      result = bbFormula(node[0]);
      for (unsigned i = 1; i < node.getNumChildren(); ++i) {
        Abc_Obj_t* child = bbFormula(node[i]);
        result = mkXor(result, child);
      }
      break;
    }
  case kind::IMPLIES:
    {
      Assert(node.getNumChildren() == 2);
      Abc_Obj_t* child1 = bbFormula(node[0]);
      Abc_Obj_t* child2 = bbFormula(node[1]);

      result = mkOr(mkNot(child1), child2);
      break;
    }
  case kind::ITE:
    {
      Assert(node.getNumChildren() == 3);
      Abc_Obj_t* a = bbFormula(node[0]);
      Abc_Obj_t* b = bbFormula(node[1]);
      Abc_Obj_t* c = bbFormula(node[2]);
      result = mkIte(a, b, c); 
      break;
    }
  case kind::NOT:
    {
      Abc_Obj_t* child1 = bbFormula(node[0]);
      result = mkNot(child1);
      break;
    }
  case kind::CONST_BOOLEAN:
    {
      result = node.getConst<bool>() ? mkTrue<Abc_Obj_t*>() : mkFalse<Abc_Obj_t*>(); 
      break;
    }
  case kind::EQUAL:
    {
      if( node[0].getType().isBoolean() ){
        Assert(node.getNumChildren() == 2);
        Abc_Obj_t* child1 = bbFormula(node[0]);
        Abc_Obj_t* child2 = bbFormula(node[1]);
  
        result = mkIff(child1, child2); 
        break;
      }
      //else, continue...
    }
  default:
    if( node.isVar() ){
      result = mkInput(node);
    }else{
      bbAtom(node);
      result = getBBAtom(node);
    }
  }

  cacheAig(node, result);
  Debug("bitvector-aig") << "AigBitblaster::bbFormula done " << node << " => " << result <<"\n"; 
  return result; 
}

void AigBitblaster::bbAtom(TNode node) {
  if (hasBBAtom(node)) {
    return;
  }

  Debug("bitvector-bitblast") << "Bitblasting atom " << node <<"\n";

  // the bitblasted definition of the atom
  Node normalized = Rewriter::rewrite(node);
  Abc_Obj_t* atom_bb = (d_atomBBStrategies[normalized.getKind()])(normalized, this);
  storeBBAtom(node, atom_bb);
  Debug("bitvector-bitblast") << "Done bitblasting atom " << node <<"\n";
}

void AigBitblaster::bbTerm(TNode node, Bits& bits) {
  if (hasBBTerm(node)) {
    getBBTerm(node, bits);
    return;
  }
  Assert(node.getType().isBitVector());

  Debug("bitvector-bitblast") << "Bitblasting term " << node <<"\n";
  d_termBBStrategies[node.getKind()] (node, bits, this);

  Assert(bits.size() == utils::getSize(node));
  storeBBTerm(node, bits);
}


void AigBitblaster::cacheAig(TNode node, Abc_Obj_t* aig) {
  Assert(!hasAig(node));
  d_aigCache.insert(std::make_pair(node, aig));
}
bool AigBitblaster::hasAig(TNode node) {
  return d_aigCache.find(node) != d_aigCache.end(); 
}
Abc_Obj_t* AigBitblaster::getAig(TNode node) {
  Assert(hasAig(node));
  Debug("bitvector-aig") << "AigSimplifer::getAig " << node << " => " << d_aigCache.find(node)->second <<"\n"; 
  return d_aigCache.find(node)->second; 
}

void AigBitblaster::makeVariable(TNode node, Bits& bits) {
  
  for (unsigned i = 0; i < utils::getSize(node); ++i) {
    Node bit = utils::mkBitOf(node, i);
    Abc_Obj_t* input = mkInput(bit);
    cacheAig(bit, input); 
    bits.push_back(input); 
  }
}

Abc_Obj_t* AigBitblaster::mkInput(TNode input) {
  Assert(!hasInput(input));
  Assert(input.getKind() == kind::BITVECTOR_BITOF
         || (input.getType().isBoolean() && input.isVar()));
  Abc_Obj_t* aig_input = Abc_NtkCreatePi(currentAigNtk());
  // d_aigCache.insert(std::make_pair(input, aig_input));
  d_nodeToAigInput.insert(std::make_pair(input, aig_input));
  Debug("bitvector-aig") << "AigSimplifer::mkInput " << input << " " << aig_input <<"\n"; 
  return aig_input; 
}

bool AigBitblaster::hasInput(TNode input) {
  return d_nodeToAigInput.find(input) != d_nodeToAigInput.end(); 
}

bool AigBitblaster::solve(TNode node) {
  // setting output of network to be the query
  Assert(d_aigOutputNode == NULL);
  Abc_Obj_t* query = bbFormula(node);
  d_aigOutputNode = Abc_NtkCreatePo(currentAigNtk());
  Abc_ObjAddFanin(d_aigOutputNode, query); 

  simplifyAig();
  convertToCnfAndAssert();
  // no need to use abc anymore
  
  TimerStat::CodeTimer solveTimer(d_statistics.d_solveTime);
  prop::SatValue result = d_satSolver->solve();

  Assert(result != prop::SAT_VALUE_UNKNOWN);
  return result == prop::SAT_VALUE_TRUE; 
}


void addAliases(Abc_Frame_t* pAbc);

void AigBitblaster::simplifyAig() {
  TimerStat::CodeTimer simpTimer(d_statistics.d_simplificationTime);

  Abc_AigCleanup(currentAigM());
  Assert(Abc_NtkCheck(currentAigNtk()));

  const char* command = options::bitvectorAigSimplifications().c_str(); 
  Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
  Abc_FrameSetCurrentNetwork(pAbc, currentAigNtk());

  addAliases(pAbc); 
  if ( Cmd_CommandExecute( pAbc, command ) ) {
    fprintf( stdout, "Cannot execute command \"%s\".\n", command );
    exit(-1); 
  }
  s_abcAigNetwork = Abc_FrameReadNtk(pAbc);
}


void AigBitblaster::convertToCnfAndAssert() {
  TimerStat::CodeTimer cnfConversionTimer(d_statistics.d_cnfConversionTime);
  
  Aig_Man_t * pMan = NULL;
  Cnf_Dat_t * pCnf = NULL;
  Assert(Abc_NtkIsStrash(currentAigNtk()));

  // convert to the AIG manager
  pMan = Abc_NtkToDar(currentAigNtk(), 0, 0 );
  Abc_Stop(); 

  // // free old network
  // Abc_NtkDelete(currentAigNtk());
  // s_abcAigNetwork = NULL;

  Assert(pMan != NULL);
  Assert(Aig_ManCheck(pMan));
  pCnf = Cnf_DeriveFast( pMan, 0 );

  assertToSatSolver(pCnf); 
    
  Cnf_DataFree( pCnf );
  Cnf_ManFree();
  Aig_ManStop(pMan);
}

void AigBitblaster::assertToSatSolver(Cnf_Dat_t* pCnf) {
  unsigned numVariables = pCnf->nVars;
  unsigned numClauses = pCnf->nClauses;
  
  d_statistics.d_numVariables += numVariables; 
  d_statistics.d_numClauses += numClauses; 

  // create variables in the sat solver
  std::vector<prop::SatVariable> sat_variables;
  for (unsigned i = 0; i < numVariables; ++i) {
    sat_variables.push_back(d_satSolver->newVar(false, false, false)); 
  }

  // construct clauses and add to sat solver
  int * pLit, * pStop;
  for (unsigned i = 0; i < numClauses; i++ ) {
    prop::SatClause clause; 
    for (pLit = pCnf->pClauses[i], pStop = pCnf->pClauses[i+1]; pLit < pStop; pLit++ ) {
      int int_lit = Cnf_Lit2Var(*pLit);
      Assert(int_lit != 0);
      unsigned index = int_lit < 0? -int_lit : int_lit;
      Assert(index - 1 < sat_variables.size());
      prop::SatLiteral lit(sat_variables[index-1], int_lit < 0); 
      clause.push_back(lit); 
    }
    d_satSolver->addClause(clause, false);
  }
}

void addAliases(Abc_Frame_t* pAbc) {
  std::vector<std::string> aliases;
  aliases.push_back("alias b balance");
  aliases.push_back("alias rw rewrite");
  aliases.push_back("alias rwz rewrite -z");
  aliases.push_back("alias rf refactor");
  aliases.push_back("alias rfz refactor -z");
  aliases.push_back("alias re restructure");
  aliases.push_back("alias rez restructure -z");
  aliases.push_back("alias rs resub");
  aliases.push_back("alias rsz resub -z");
  aliases.push_back("alias rsk6 rs -K 6");
  aliases.push_back("alias rszk5 rsz -K 5");
  aliases.push_back("alias bl b -l");
  aliases.push_back("alias rwl rw -l");
  aliases.push_back("alias rwzl rwz -l");
  aliases.push_back("alias rwzl rwz -l");
  aliases.push_back("alias rfl rf -l");
  aliases.push_back("alias rfzl rfz -l");
  aliases.push_back("alias brw \"b; rw\"");

  for (unsigned i = 0; i < aliases.size(); ++i) {
    if ( Cmd_CommandExecute( pAbc, aliases[i].c_str() ) ) {
      fprintf( stdout, "Cannot execute command \"%s\".\n", aliases[i].c_str() );
      exit(-1); 
    }
  }
}

bool AigBitblaster::hasBBAtom(TNode atom) const {
  return d_bbAtoms.find(atom) != d_bbAtoms.end(); 
}

void AigBitblaster::storeBBAtom(TNode atom, Abc_Obj_t* atom_bb) {
  d_bbAtoms.insert(std::make_pair(atom, atom_bb)); 
}

Abc_Obj_t* AigBitblaster::getBBAtom(TNode atom) const {
  Assert(hasBBAtom(atom));
  return d_bbAtoms.find(atom)->second;
}

AigBitblaster::Statistics::Statistics()
  : d_numClauses("theory::bv::AigBitblaster::numClauses", 0)
  , d_numVariables("theory::bv::AigBitblaster::numVariables", 0)
  , d_simplificationTime("theory::bv::AigBitblaster::simplificationTime")
  , d_cnfConversionTime("theory::bv::AigBitblaster::cnfConversionTime")
  , d_solveTime("theory::bv::AigBitblaster::solveTime")
{
  smtStatisticsRegistry()->registerStat(&d_numClauses); 
  smtStatisticsRegistry()->registerStat(&d_numVariables);
  smtStatisticsRegistry()->registerStat(&d_simplificationTime); 
  smtStatisticsRegistry()->registerStat(&d_cnfConversionTime);
  smtStatisticsRegistry()->registerStat(&d_solveTime); 
}

AigBitblaster::Statistics::~Statistics() {
  smtStatisticsRegistry()->unregisterStat(&d_numClauses); 
  smtStatisticsRegistry()->unregisterStat(&d_numVariables);
  smtStatisticsRegistry()->unregisterStat(&d_simplificationTime); 
  smtStatisticsRegistry()->unregisterStat(&d_cnfConversionTime);
  smtStatisticsRegistry()->unregisterStat(&d_solveTime); 
}

}  // namespace bv
}  // namespace theory
}  // namespace CVC4
#endif // CVC4_USE_ABC
