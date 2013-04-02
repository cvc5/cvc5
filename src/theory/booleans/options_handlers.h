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
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BOOLEANS__OPTIONS_HANDLERS_H
#define __CVC4__THEORY__BOOLEANS__OPTIONS_HANDLERS_H

#include <string>

namespace CVC4 {
namespace theory {
namespace booleans {

static const std::string booleanTermConversionModeHelp = "\
Boolean term conversion modes currently supported by the\n\
--boolean-term-conversion-mode option:\n\
\n\
bitvectors [default]\n\
+ Boolean terms are converted to bitvectors of size 1.\n\
\n\
datatypes\n\
+ Boolean terms are converted to enumerations in the Datatype theory.\n\
\n\
native\n\
+ Boolean terms are converted in a \"natural\" way depending on where they\n\
  are used.  If in a datatype context, they are converted to an enumeration.\n\
  Elsewhere, they are converted to a bitvector of size 1.\n\
";

inline BooleanTermConversionMode stringToBooleanTermConversionMode(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if(optarg ==  "bitvectors") {
    return BOOLEAN_TERM_CONVERT_TO_BITVECTORS;
  } else if(optarg ==  "datatypes") {
    return BOOLEAN_TERM_CONVERT_TO_DATATYPES;
  } else if(optarg ==  "native") {
    return BOOLEAN_TERM_CONVERT_NATIVE;
  } else if(optarg ==  "help") {
    puts(booleanTermConversionModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --boolean-term-conversion-mode: `") +
                          optarg + "'.  Try --boolean-term-conversion-mode help.");
  }
}

}/* CVC4::theory::booleans namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BOOLEANS__OPTIONS_HANDLERS_H */
