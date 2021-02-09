/*********************                                                        */
/*! \file inst_strategy.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Instantiation Engine classes
 **/

#include "theory/quantifiers/inst_strategy.h"
#include "theory/quantifiers/quantifiers_state.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

  InstStrategy::InstStrategy(QuantifiersEngine* qe,
               QuantifiersState& qs,
               QuantifiersInferenceManager& qim)
      : d_quantEngine(qe), d_qstate(qs), d_qim(qim)
  {
  }
 InstStrategy:: ~InstStrategy() {}
void InstStrategy::presolve() {}
std::string InstStrategy::identify() const { return std::string("Unknown"); }

options::UserPatMode InstStrategy::getInstUserPatMode()
{
  if (options::userPatternsQuant() == options::UserPatMode::INTERLEAVE)
  {
    return d_qstate.getInstRounds() % 2 == 0 ? options::UserPatMode::USE
                                             : options::UserPatMode::RESORT;
  }
  return options::userPatternsQuant();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

