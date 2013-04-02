/*********************                                                        */
/*! \file options_holder_template.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Global (command-line, set-option, ...) parameters for SMT
 **
 ** Global (command-line, set-option, ...) parameters for SMT.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__OPTIONS__OPTIONS_HOLDER_H
#define __CVC4__OPTIONS__OPTIONS_HOLDER_H

${include_all_option_headers}

#line 25 "${template}"

namespace CVC4 {
namespace options {

struct OptionsHolder {
  OptionsHolder();
${all_modules_contributions}

#line 34 "${template}"

};/* struct OptionsHolder */

}/* CVC4::options namespace */
}/* CVC4 namespace */

#endif /* __CVC4__OPTIONS__OPTIONS_HOLDER_H */
