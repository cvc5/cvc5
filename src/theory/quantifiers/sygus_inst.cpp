/*********************                                                        */
/*! \file sygus_inst.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SyGuS instantiator class.
 **/

#include "theory/quantifiers/sygus_inst.h"

#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusInst::SygusInst(QuantifiersEngine* qe) : QuantifiersModule(qe) {}

// Note: Called once per q (context-independent initialization)
void SygusInst::registerQuantifier(Node q)
{
  std::cout << identify() << "::register: " << q << std::endl;
}

// Note: Called once per SAT context
void SygusInst::preRegisterQuantifier(Node q)
{
  std::cout << identify() << "::preRegister: " << q << std::endl;
}

void SygusInst::check(Theory::Effort e, QEffort quant_e)
{
  std::cout << identify() << "::check " << e << ", " << quant_e << std::endl;

  // Notes:
  //
  // * check active quantifiers via FirstOrderModel d_quantEngine->getModel()
  //
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
