/*********************                                                        */
/*! \file command_list.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A context-sensitive list of Commands, and their cleanup
 **
 ** A context-sensitive list of Commands, and their cleanup.
 **/

// we include both of these to make sure they agree on the typedef
#include "smt/command_list.h"
#include "smt/smt_engine.h"

#include "expr/command.h"

namespace CVC4 {
namespace smt {

void CommandCleanup::operator()(Command** c) {
  delete *c;
}

}/* CVC4::smt namespace */
}/* CVC4 namespace */
