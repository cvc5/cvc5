/*********************                                                        */
/*! \file smt_engine_scope.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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
