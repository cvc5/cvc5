/*********************                                                        */
/*! \file smt_options_template.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Option handling for SmtEngine
 **
 ** Option handling for SmtEngine.
 **/

#include "smt/smt_engine.h"
#include "smt/bad_option_exception.h"
#include "smt/modal_exception.h"
#include "util/sexpr.h"
#include "util/dump.h"
#include "expr/command.h"
#include "expr/node_manager.h"

#include <string>
#include <sstream>

${include_all_option_headers}
${option_handler_includes}

#line 34 "${template}"

using namespace std;

namespace CVC4 {

void SmtEngine::setOption(const std::string& key, const CVC4::SExpr& value)
  throw(BadOptionException, ModalException) {

  NodeManagerScope nms(d_nodeManager);
  SmtEngine* const smt = this;

  Trace("smt") << "SMT setOption(" << key << ", " << value << ")" << endl;
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << SetOptionCommand(key, value);
  }

  string optarg = value.getValue();

  ${smt_setoption_handlers}

#line 55 "${template}"

  throw BadOptionException();
}

CVC4::SExpr SmtEngine::getOption(const std::string& key) const
  throw(BadOptionException) {

  NodeManagerScope nms(d_nodeManager);

  Trace("smt") << "SMT getOption(" << key << ")" << endl;
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetOptionCommand(key);
  }

  ${smt_getoption_handlers}

#line 72 "${template}"

  throw BadOptionException();
}

}/* CVC4 namespace */
