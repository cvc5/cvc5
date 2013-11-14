/*********************                                                        */
/*! \file aig.h
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

#include "expr/node.h"
#include "base/main/main.h"
#include "base/abc/abc.h"

class Cnf_Dat_t_;
typedef Cnf_Dat_t_ Cnf_Dat_t;


namespace CVC4 {

namespace prop {
class BVSatSolverInterface;
}


namespace theory {
namespace bv {

class AigSimplifier; 

class AigBitblaster : public Bitblaster {
private:
  AigSimplifier* d_aigSimplifer; 
  void addAtom(TNode atom);
public:
  void storeVariable(TNode node);
  void bbTerm(TNode node, Bits&  bits);
  void bbAtom(TNode node);
  /** 
   * Ensures that all the atoms in formula have been
   * converted to AIG
   * 
   * @param formula 
   */
  void bbFormula(TNode formula);
  
  AigBitblaster(AigSimplifier* aigSimplifier); 
  ~AigBitblaster();
};

class AigSimplifier {
  Abc_Ntk_t* d_abcAigNetwork;
  prop::BVSatSolverInterface* d_satSolver;
  // invalidates all the maps and caches
  bool d_asserted;
  typedef std::hash_map<Node, Abc_Obj_t*, NodeHashFunction > NodeAigMap;
  // typedef std::hash_map<Abc_Obj_t*, TNode > AigTNodeMap;
  NodeAigMap d_aigCache;
  NodeAigMap d_nodeToAigInput;
  // AigTNodeMap d_aigInputToNode;
  
  Abc_Obj_t* d_trueAigNode;
  Abc_Obj_t* d_falseAigNode;

  AigBitblaster* d_bitblaster;
  Abc_Obj_t* d_aigOutputNode;
  
  void cacheAig(TNode node, Abc_Obj_t* aig);
  bool hasAig(TNode node);
  Abc_Obj_t* getAig(TNode node);

  void assertToSatSolver(Cnf_Dat_t* pCnf);
  void convertToCnf(Abc_Ntk_t * pNtk);
public:
  /** 
   * Construct an AIG simplifier that will bit-blast to the given
   * SatSolver. 
   * 
   * @param satSolver 
   */
  AigSimplifier(prop::BVSatSolverInterface* satSolver);
  ~AigSimplifier();
  /** 
   * Convert given formula to AIG format and add to the current
   * network. 
   * 
   * @param formula 
   */
  Abc_Obj_t* convertToAig(TNode formula);

  /** 
   * Creates a fresh input for the given TNode. This has
   * to be either a Boolean Variable or a BIT_OF kind.
   * 
   * @param input 
   * 
   * @return 
   */
  void mkInput(TNode input); 
  Abc_Obj_t* getInput(TNode input);
  bool hasInput(TNode input); 
  /** 
   * Run AIG simplifications on the network and assert it to the
   * SatSolver. 
   * 
   */
  void simplifyAig();
  void convertToCnfAndAssert(); 
  void setOutput(TNode query);
  /** 
   * Check if the current formulas are satisfiable
   * 
   * @return 
   */
  bool solve();
  friend class AigBitblaster; 

  class Statistics {
  public:
    IntStat     d_numClauses;
    IntStat     d_numVariables; 
    TimerStat   d_simplificationTime;
    TimerStat   d_cnfConversionTime;
    TimerStat   d_solveTime; 
    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;

};
}
}
}
