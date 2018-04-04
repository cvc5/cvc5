/*********************                                                        */
/*! \file options_holder.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Global (command-line, set-option, ...) parameters for SMT
 **
 ** Global (command-line, set-option, ...) parameters for SMT.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__OPTIONS__OPTIONS_HOLDER_H
#define __CVC4__OPTIONS__OPTIONS_HOLDER_H

${headers_module}$


namespace CVC4 {
namespace options {

struct OptionsHolder {
  OptionsHolder();
  ${macros_module}$


};/* struct OptionsHolder */

}  // namespace options
}  // namespace CVC4

#endif /* __CVC4__OPTIONS__OPTIONS_HOLDER_H */
