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
 ** \brief Custom handlers and predicates for TheoryUF options
 **
 ** Custom handlers and predicates for TheoryUF options.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__UF__OPTIONS_HANDLERS_H
#define __CVC4__THEORY__UF__OPTIONS_HANDLERS_H

namespace CVC4 {
namespace theory {
namespace uf {
  
typedef enum {
  /** default, use uf strong solver to find minimal models for uninterpreted sorts */
  UF_SS_FULL,
  /** use uf strong solver to shrink model sizes, but do no enforce minimality */
  UF_SS_NO_MINIMAL,
  /** do not use uf strong solver */
  UF_SS_NONE,
} UfssMode;
  
static const std::string ufssModeHelp = "\
UF strong solver options currently supported by the --uf-ss option:\n\
\n\
full \n\
+ Default, use uf strong solver to find minimal models for uninterpreted sorts.\n\
\n\
no-minimal \n\
+ Use uf strong solver to shrink model sizes, but do no enforce minimality.\n\
\n\
none \n\
+ Do not use uf strong solver to shrink model sizes. \n\
\n\
";

inline UfssMode stringToUfssMode(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if(optarg ==  "default" || optarg == "full" ) {
    return UF_SS_FULL;
  } else if(optarg == "no-minimal") {
    return UF_SS_NO_MINIMAL;
  } else if(optarg == "none") {
    return UF_SS_NONE;
  } else if(optarg ==  "help") {
    puts(ufssModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --uf-ss: `") +
                          optarg + "'.  Try --uf-ss help.");
  }
}

}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__UF__OPTIONS_HANDLERS_H */

