/*********************                                                        */
/*! \file options_holder_template.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Global (command-line, set-option, ...) parameters for SMT
 **
 ** Global (command-line, set-option, ...) parameters for SMT.
 **/

#include "cvc4_private.h"

#ifndef CVC4__OPTIONS__OPTIONS_HOLDER_H
#define CVC4__OPTIONS__OPTIONS_HOLDER_H

${headers_module}$


namespace CVC4 {
namespace options {

struct OptionsHolder {
  OptionsHolder();
  ${macros_module}$


};/* struct OptionsHolder */

}  // namespace options
}  // namespace CVC4

#endif /* CVC4__OPTIONS__OPTIONS_HOLDER_H */
