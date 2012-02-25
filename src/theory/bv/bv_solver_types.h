//*********************                                                        */
/*! \file bv_solver_types.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Definitions of the SatSolver literal and clause types 
 **
 **/

#include "cvc4_private.h"

#ifndef __CVC4__BV__SOLVER__TYPES_H 
#define __CVC4__BV__SOLVER__TYPES_H 

#define BV_MINISAT
//#define BV_PICOSAT

#ifdef BV_MINISAT  /* BV_MINISAT if we are using the minisat solver for the theory of bitvectors*/
#include "theory/bv/bvminisat/core/Solver.h"
#include "theory/bv/bvminisat/core/SolverTypes.h"
#include "theory/bv/bvminisat/simp/SimpSolver.h"
#endif   /* BV_MINISAT */

#ifdef BV_PICOSAT  /* BV_PICOSAT */
#include "picosat/picosat.h"
#endif  /* BV_PICOSAT */

#include "expr/node.h"
#include <vector>
#include <list>
#include <iostream>
#include <math.h>
#include <ext/hash_map>
#include "context/cdlist.h"
#include "util/stats.h"


namespace CVC4 {
namespace theory {
namespace bv {

#endif /* BV_MINISAT */



// #ifdef BV_PICOSAT /* BV_PICOSAT */
// /** 
//  * PICOSAT type-definitions
//  * 
//  * 
//  */

// typedef int SatVar; 
// typedef int SatLit; 

// std::string toStringLit(SatLit lit); 


// SatLit neg(const SatLit& lit); 

// struct SatLitHash {
//   static size_t hash (const SatLit& lit) {
//     return (size_t) lit;
//   }
  
// };

// struct SatLitHashFunction {
//   size_t operator()(SatLit lit) const {
//     return (size_t) lit; 
//   }
// };

// struct SatLitLess{
//   static bool compare(const SatLit& x, const SatLit& y)
//   {
//     return x < y;
//   }
// };

// #endif /* BV_PICOSAT */

// #ifdef BV_PICOSAT  /* BV_PICOSAT */

// /** 
//  * Some helper functions that should be defined for each SAT solver supported
//  * 
//  * 
//  * @return 
//  */

// SatLit mkLit(SatVar var);
// SatVar mkVar(SatLit lit);
// bool   polarity(SatLit lit); 


// /** 
//  * Wrapper to create the impression of a SatSolver class for Picosat
//  * which is written in C
//  */

// class SatSolver: public SatSolverInterface {
//   int d_varCount;
//   bool d_started;
// public:
//   SatSolver() :
//     d_varCount(0),
//     d_started(false)
//   {
//     picosat_init(); /// call constructor
//     picosat_enable_trace_generation(); // required for unsat cores
//   }
  
//   ~SatSolver() {
//     picosat_reset(); 
//   }

//   void   addClause(const SatClause* cl) {
//     Assert (cl);
//     const SatClause& clause = *cl; 
//     for (unsigned i = 0; i < clause.size(); ++i ) {
//       picosat_add(clause[i]); 
//     }
//     picosat_add(0); // ends clause
//   }
  
//   bool   solve () {
//     if(d_started) {
//       picosat_remove_learned(100);
//     }
//     int res = picosat_sat(-1); // no decision limit
//     // 0 UNKNOWN, 10 SATISFIABLE and 20 UNSATISFIABLE
//     d_started = true; 
//     Assert (res == 10 || res == 20); 
//     return res == 10; 
//   }
  
//   bool   solve(const context::CDList<SatLit> & assumps) {
//     context::CDList<SatLit>::const_iterator it = assumps.begin();
//     for (; it!= assumps.end(); ++it) {
//       picosat_assume(*it); 
//     }
//     return solve (); 
//   }
  
//   SatVar newVar() { return ++d_varCount; }

//   void   setUnremovable(SatLit lit) {}; 

//   SatClause* getUnsatCore() {
//     const int* failedAssumption = picosat_failed_assumptions();
//     Assert(failedAssumption);

//     SatClause* unsatCore = new SatClause();
//     while (*failedAssumption != 0) {
//       SatLit lit = *failedAssumption;
//       unsatCore->addLiteral(neg(lit));
//       ++failedAssumption; 
//     }
//     unsatCore->sort(); 
//     return unsatCore; 
//   }
// }; 


// #endif  /* BV_PICOSAT */




} /* bv namespace */ 

} /* theory namespace */

} /* CVC4 namespace */

#endif /* __CVC4__BV__SOLVER__TYPES_H */
