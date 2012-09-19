/*********************                                                        */
/*! \file command_list.h
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

#include "cvc4_private.h"

#ifndef __CVC4__SMT__COMMAND_LIST_H
#define __CVC4__SMT__COMMAND_LIST_H

#include "context/cdlist.h"

namespace CVC4 {

class Command;

namespace smt {

struct CommandCleanup {
  void operator()(Command** c);
};/* struct CommandCleanup */

typedef context::CDList<Command*, CommandCleanup> CommandList;

}/* CVC4::smt namespace */
}/* CVC4 namespace */

#endif /* __CVC4__SMT__COMMAND_LIST_H */
