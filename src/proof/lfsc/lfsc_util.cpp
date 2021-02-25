/*********************                                                        */
/*! \file lfsc_printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing Lfsc proof nodes
 **/

#include "proof/lfsc/lfsc_util.h"

namespace CVC4 {
namespace proof {

const char* toString(LfscRule id)
{
  switch (id)
  {
    case LfscRule::SYMM: return "symm";
    case LfscRule::NEG_SYMM: return "neg_symm";
    case LfscRule::CONG: return "cong";
    case LfscRule::TRANS: return "trans";
    case LfscRule::CNF_AND_POS_1: return "cnf_and_pos_1";
    case LfscRule::CNF_AND_POS_2: return "cnf_and_pos_2";
    default: return "?";
  }
}
std::ostream& operator<<(std::ostream& out, LfscRule id)
{
  out << toString(id);
  return out;
}

}  // namespace proof
}  // namespace CVC4
