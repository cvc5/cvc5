/*********************                                                        */
/*! \file options_handlers.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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

#include "util/output.h"
#include "util/dump.h"

namespace CVC4 {
namespace expr {

inline void setDefaultExprDepth(std::string option, int depth, SmtEngine* smt) {
  if(depth < -1) {
    throw OptionException("--default-expr-depth requires a positive argument, or -1.");
  }

  Debug.getStream() << Expr::setdepth(depth);
  Trace.getStream() << Expr::setdepth(depth);
  Notice.getStream() << Expr::setdepth(depth);
  Chat.getStream() << Expr::setdepth(depth);
  Message.getStream() << Expr::setdepth(depth);
  Warning.getStream() << Expr::setdepth(depth);
  // intentionally exclude Dump stream from this list
}

inline void setDefaultDagThresh(std::string option, int dag, SmtEngine* smt) {
  if(dag < 0) {
    throw OptionException("--default-dag-thresh requires a nonnegative argument.");
  }

  Debug.getStream() << Expr::dag(dag);
  Trace.getStream() << Expr::dag(dag);
  Notice.getStream() << Expr::dag(dag);
  Chat.getStream() << Expr::dag(dag);
  Message.getStream() << Expr::dag(dag);
  Warning.getStream() << Expr::dag(dag);
  Dump.getStream() << Expr::dag(dag);
}

inline void setPrintExprTypes(std::string option, SmtEngine* smt) {
  Debug.getStream() << Expr::printtypes(true);
  Trace.getStream() << Expr::printtypes(true);
  Notice.getStream() << Expr::printtypes(true);
  Chat.getStream() << Expr::printtypes(true);
  Message.getStream() << Expr::printtypes(true);
  Warning.getStream() << Expr::printtypes(true);
  // intentionally exclude Dump stream from this list
}

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* __CVC4__EXPR__OPTIONS_HANDLERS_H */
