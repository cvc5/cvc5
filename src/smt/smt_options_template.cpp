/*********************                                                        */
/*! \file smt_options_template.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Option handling for SmtEngine
 **
 ** Option handling for SmtEngine.
 **/

#include "smt/smt_engine.h"
#include "smt/modal_exception.h"
#include "util/sexpr.h"
#include "util/dump.h"
#include "expr/command.h"
#include "expr/node_manager.h"

#include <string>
#include <sstream>

${include_all_option_headers}
${option_handler_includes}

#line 31 "${template}"

using namespace std;

namespace CVC4 {

void SmtEngine::setOption(const std::string& key, const CVC4::SExpr& value)
  throw(OptionException, ModalException) {

  NodeManagerScope nms(d_nodeManager);
  SmtEngine* const smt = this;

  Trace("smt") << "SMT setOption(" << key << ", " << value << ")" << endl;
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << SetOptionCommand(key, value);
  }

  if(key == "command-verbosity") {
    if(!value.isAtom()) {
      const vector<SExpr>& cs = value.getChildren();
      if(cs.size() == 2 &&
         (cs[0].isKeyword() || cs[0].isString()) &&
         cs[1].isInteger()) {
        string c = cs[0].getValue();
        const Integer& v = cs[1].getIntegerValue();
        if(v < 0 || v > 2) {
          throw OptionException("command-verbosity must be 0, 1, or 2");
        }
        d_commandVerbosity[c] = v;
        return;
      }
    }
    throw OptionException("command-verbosity value must be a tuple (command-name, integer)");
  }

  if(!value.isAtom()) {
    throw OptionException("bad value for :" + key);
  }

  string optionarg = value.getValue();

  ${smt_setoption_handlers}

#line 74 "${template}"

  throw UnrecognizedOptionException(key);
}

CVC4::SExpr SmtEngine::getOption(const std::string& key) const
  throw(OptionException) {

  NodeManagerScope nms(d_nodeManager);

  Trace("smt") << "SMT getOption(" << key << ")" << endl;

  if(key.length() >= 18 &&
     key.compare(0, 18, "command-verbosity:") == 0) {
    map<string, Integer>::const_iterator i = d_commandVerbosity.find(key.c_str() + 18);
    if(i != d_commandVerbosity.end()) {
      return (*i).second;
    }
    i = d_commandVerbosity.find("*");
    if(i != d_commandVerbosity.end()) {
      return (*i).second;
    }
    return Integer(2);
  }

  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetOptionCommand(key);
  }

  if(key == "command-verbosity") {
    vector<SExpr> result;
    SExpr defaultVerbosity;
    for(map<string, Integer>::const_iterator i = d_commandVerbosity.begin();
        i != d_commandVerbosity.end();
        ++i) {
      vector<SExpr> v;
      v.push_back((*i).first);
      v.push_back((*i).second);
      if((*i).first == "*") {
        // put the default at the end of the SExpr
        defaultVerbosity = v;
      } else {
        result.push_back(v);
      }
    }
    // put the default at the end of the SExpr
    if(!defaultVerbosity.isAtom()) {
      result.push_back(defaultVerbosity);
    } else {
      // ensure the default is always listed
      vector<SExpr> v;
      v.push_back("*");
      v.push_back(Integer(2));
      result.push_back(v);
    }
    return result;
  }

  ${smt_getoption_handlers}

#line 134 "${template}"

  throw UnrecognizedOptionException(key);
}

}/* CVC4 namespace */
