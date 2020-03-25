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
 * The purpose of this method is to set the default options and update the logic
 * info for SMT engine smte.
 * 
 * The argument logic is a reference to the logic of SmtEngine, which can be
 * updated based on the options.
 * 
 * Currently, options are associated with the ExprManager. Thus, this
 * call updates the options associated with the current ExprManager.
 * If this designed is updated in the future so that SmtEngine has its own
 * copy of options, this method should be updated accordingly.
 */
void setDefaults(SmtEngine& smte, LogicInfo& logic);
  
}
}

#endif /* CVC4__SMT__SET_DEFAULTS_H */
