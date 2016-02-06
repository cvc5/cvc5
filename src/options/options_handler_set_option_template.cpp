/*********************                                                        */
/*! \file option_handler_set_option_template.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of OptionsHandler::setOption.
 **
 ** This template file is expanded into the cpp implementation of
 ** OptionsHandler::setOption. The file is essentially the contents
 ** of the ${smt_setoption_handlers} variable in the options/mkoptions
 ** script. This variable depends on all options files. To generate this file,
 ** first generate options/summary.sed.
 **/

#include <string>
#include <sstream>

#include "base/output.h"
#include "base/modal_exception.h"
#include "options/option_exception.h"
#include "options/options_handler_interface.h"


${include_all_option_headers}
${option_handler_includes}

#line 31 "${template}"

using namespace std;

namespace CVC4 {
namespace options {

void OptionsHandler::setOption(const std::string& key, const std::string& optionarg)
  throw(OptionException, ModalException) {
  options::OptionsHandler* const handler = this;
  Trace("options") << "SMT setOption(" << key << ", " << optionarg << ")" << endl;

  ${smt_setoption_handlers}

#line 44 "${template}"

  throw UnrecognizedOptionException(key);
}

}/* options namespace */
}/* CVC4 namespace */
