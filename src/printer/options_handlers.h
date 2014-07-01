/*********************                                                        */
/*! \file options_handlers.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Custom handlers and predicates for printer options
 **
 ** Custom handlers and predicates for printer options.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PRINTER__OPTIONS_HANDLERS_H
#define __CVC4__PRINTER__OPTIONS_HANDLERS_H

#include "printer/modes.h"

namespace CVC4 {
namespace printer {

static const std::string modelFormatHelp = "\
Model format modes currently supported by the --model-format option:\n\
\n\
default \n\
+ Print model as expressions in the output language format.\n\
\n\
table\n\
+ Print functional expressions over finite domains in a table format.\n\
";

static const std::string instFormatHelp = "\
Inst format modes currently supported by the --model-format option:\n\
\n\
default \n\
+ Print instantiations as a list in the output language format.\n\
\n\
szs\n\
+ Print instantiations as SZS compliant proof.\n\
";

inline ModelFormatMode stringToModelFormatMode(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if(optarg == "default") {
    return MODEL_FORMAT_MODE_DEFAULT;
  } else if(optarg == "table") {
    return MODEL_FORMAT_MODE_TABLE;
  } else if(optarg == "help") {
    puts(modelFormatHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --model-format: `") +
                          optarg + "'.  Try --model-format help.");
  }
}

inline InstFormatMode stringToInstFormatMode(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if(optarg == "default") {
    return INST_FORMAT_MODE_DEFAULT;
  } else if(optarg == "szs") {
    return INST_FORMAT_MODE_SZS;
  } else if(optarg == "help") {
    puts(instFormatHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --inst-format: `") +
                          optarg + "'.  Try --inst-format help.");
  }
}
}/* CVC4::printer namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PRINTER__OPTIONS_HANDLERS_H */
