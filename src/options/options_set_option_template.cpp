/*********************                                                        */
/*! \file options_set_option_template.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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

#include "base/modal_exception.h"
#include "base/output.h"
#include "options/option_exception.h"
#include "options/options.h"
#include "options/options_handler.h"

${include_all_option_headers}
${option_handler_includes}

#line 35 "${template}"

using namespace std;

namespace CVC4 {

void Options::setOption(const std::string& key, const std::string& optionarg)
  throw(OptionException, ModalException) {
  options::OptionsHandler* handler = d_handler;
  Trace("options") << "SMT setOption(" << key << ", " << optionarg << ")" << endl;

  ${smt_setoption_handlers}

#line 48 "${template}"

  throw UnrecognizedOptionException(key);
}

}/* CVC4 namespace */
