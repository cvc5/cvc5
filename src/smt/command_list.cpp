/*********************                                                        */
/*! \file command_list.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A context-sensitive list of Commands, and their cleanup
 **
 ** A context-sensitive list of Commands, and their cleanup.
 **/

// we include both of these to make sure they agree on the typedef
#include "smt/command.h"
#include "smt/command_list.h"
#include "smt/smt_engine.h"

namespace CVC4 {
namespace smt {

void CommandCleanup::operator()(Command** c) {
  delete *c;
}

}/* CVC4::smt namespace */
}/* CVC4 namespace */
