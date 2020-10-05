/*********************                                                        */
/*! \file module_template.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Contains code for handling command-line options.
 **
 ** For each <module>_options.toml configuration file, mkoptions.py
 ** expands this template and generates a <module>_options.h file.
 **/

#include "cvc4_private.h"

#ifndef CVC4__OPTIONS__${id}$_H
#define CVC4__OPTIONS__${id}$_H

#include "options/options.h"

${includes}$


${holder_spec}$


namespace CVC4 {

namespace options {

${modes}$

${decls}$

}  // namespace options

${specs}$


namespace options {

${inls}$

}  // namespace options
}  // namespace CVC4

#endif /* CVC4__OPTIONS__${id}$_H */
