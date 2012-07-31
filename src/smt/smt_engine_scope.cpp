/*********************                                                        */
/*! \file smt_engine_scope.cpp
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
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"

namespace CVC4 {
namespace smt {

CVC4_THREADLOCAL(SmtEngine*) s_smtEngine_current = NULL;

}/* CVC4::smt namespace */
}/* CVC4 namespace */
