/*********************                                                        */
/*! \file sygus_repair_const.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_repair_const
 **/

#include "theory/quantifiers/sygus/sygus_repair_const.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {
  
SygusRepairConst::SygusRepairConst( QuantifiersEngine * qe ) :
d_qe(qe),
d_no_constant_grammar(true)
{

}

void SygusRepairConst::initialize( Node q )
{
  
  
}

bool SygusRepairConst::repairSolution(const std::vector< Node >& candidates, 
                    const std::vector< Node >& candidate_values, 
                    std::vector< Node >& repair_cv)
{
  Assert( candidates.size()==candidate_values.size() );
  
  // if no grammar type allows constants, no repair is possible 
  if( d_no_constant_grammar )
  {
    return false;
  }
  
  
  
  bool changed = false;
  
  for( unsigned i=0,size=candidates.size(); i<size; i++ )
  {
    Node cv = candidate_values[i];
    // get the most general candidate skeleton
    std::map<TypeNode, int> free_var_count;
    
    // TODO
  
  }
  
  if( changed )
  {
    
  }
  
  return false;
}


} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
