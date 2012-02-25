/*********************                                                        */
/*! \file bv_sat.cpp
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
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** 
 **/

#include "bv_solver_types.h"

namespace CVC4 {
namespace theory {
namespace bv {

#ifdef BV_MINISAT 
using namespace BVMinisat; 
SatLit neg(const SatLit& lit) {
  return ~lit; 
}

SatLit mkLit(SatVar var) {
  return BVMinisat::mkLit(var, false); 
}

SatVar mkVar(SatLit lit) {
  return BVMinisat::var(lit); 
}
bool   polarity(SatLit lit) {
  return !(BVMinisat::sign(lit)); 
} 


std::string toStringLit(SatLit lit) {
  std::ostringstream os;
  os << (polarity(lit) ? "" : "-") << var(lit) + 1;
  return os.str(); 
}
#endif

#ifdef BV_PICOSAT

SatLit mkLit(SatVar var) {
  return var;
}
SatVar mkVar(SatLit lit) {
  return (lit > 0 ? lit : -lit); 
}
bool   polarity(SatLit lit) {
  return (lit > 0); 
}

SatLit neg(const SatLit& lit) {
   return -lit; 
}

std::string toStringLit(SatLit lit) {
  std::ostringstream os;
  os << (lit < 0 ? "-" : "") << lit;
  return os.str(); 
}


#endif  

}
}
}
