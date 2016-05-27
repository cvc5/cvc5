/*********************                                                        */
/*! \file options_get_option_template.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of OptionsHandler::getOption.
 **
 ** This template file is expanded into the cpp implementation of
 ** OptionsHandler::setOption. The file is essentially the contents
 ** of the ${smt_getoption_handlers} variable in the options/mkoptions
 ** script. This variable depends on all options files. To generate this file,
 ** first generate options/summary.sed.
 **/

#include <iomanip>
#include <string>
#include <sstream>


#include "base/output.h"
#include "base/modal_exception.h"
#include "options/option_exception.h"
#include "options/options.h"
#include "options/options_handler.h"


${include_all_option_headers}
${option_handler_includes}

#line 37 "${template}"

using namespace std;

namespace CVC4 {

std::string Options::getOption(const std::string& key) const
  throw(OptionException) {
  Trace("options") << "SMT getOption(" << key << ")" << endl;

  ${smt_getoption_handlers}

#line 49 "${template}"

  throw UnrecognizedOptionException(key);
}

}/* CVC4 namespace */
