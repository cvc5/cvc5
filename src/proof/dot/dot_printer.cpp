/*********************                                                        */
/*! \file dot_printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Diego Camargos
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implemantation of the module for printing dot proofs
 **/

#include "proof/dot/dot_printer.h"

namespace CVC4 {
namespace proof {

void DotPrinter::print(std::ostream& out, const ProofNode* pn)
{
  out << "disgraph {}\n";
  // pn->getChildren() -> the premises (proof nodes)
  // pn->getArgs() -> the args (nodes)
  // pn->getResult() -> conclusion (node)
  // pn->getRule() -> rule used in the proof (PfRule)

}

}  // namespace proof
}  // namespace CVC4
