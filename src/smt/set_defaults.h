/*********************                                                        */
/*! \file set_defaults.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Method for setting the default options of an SMT engine.
 **/

#ifndef CVC4__SMT__SET_DEFAULTS_H
#define CVC4__SMT__SET_DEFAULTS_H

#include "smt/smt_engine.h"
#include "theory/logic_info.h"

namespace CVC4 {
namespace smt {

/** 
 * Set the default options and update the logic info for SMT engine smte.
 */
void setDefaults(SmtEngine& smte, LogicInfo& logic);
  
}
}

#endif /* CVC4__SMT__SET_DEFAULTS_H */
