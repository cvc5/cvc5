/*********************                                                        */
/*! \file options_handlers.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Custom handlers and predicates for expression package options
 **
 ** Custom handlers and predicates for expression package options.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__EXPR__OPTIONS_HANDLERS_H
#define __CVC4__EXPR__OPTIONS_HANDLERS_H

#include <string>

namespace CVC4 {
class SmtEngine;

namespace expr {


void setDefaultExprDepth(std::string option, int depth, SmtEngine* smt);

void setDefaultDagThresh(std::string option, int dag, SmtEngine* smt);

void setPrintExprTypes(std::string option, SmtEngine* smt);

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* __CVC4__EXPR__OPTIONS_HANDLERS_H */
