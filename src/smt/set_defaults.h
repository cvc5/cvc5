/*********************                                                        */
/*! \file set_defaults.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Method for setting the default options of an SMT engine.
 **/

#ifndef CVC4__SMT__SET_DEFAULTS_H
#define CVC4__SMT__SET_DEFAULTS_H

#include "theory/logic_info.h"

namespace CVC4 {
namespace smt {

/**
 * The purpose of this method is to set the default options and update the logic
 * info for an SMT engine.
 *
 * @param logic A reference to the logic of SmtEngine, which can be
 * updated by this method based on the current options and the logic itself.
 * @param isInternalSubsolver Whether we are setting the options for an
 * internal subsolver (see SmtEngine::isInternalSubsolver).
 * 
 * NOTE: we currently modify the current options in scope. This method
 * can be further refactored to modify an options object provided as an
 * explicit argument.
 */
void setDefaults(LogicInfo& logic, bool isInternalSubsolver);

}  // namespace smt
}  // namespace CVC4

#endif /* CVC4__SMT__SET_DEFAULTS_H */
