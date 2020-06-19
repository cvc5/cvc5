/*********************                                                        */
/*! \file module_template.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Option template for option modules.
 **
 ** For each <module>_options.toml configuration file, mkoptions.py
 ** expands this template and generates a <module>_options.cpp file.
 **/

#include "options/options_holder.h"
#include "base/check.h"

namespace CVC4 {

${accs}$


namespace options {

${defs}$

${modes}$

}  // namespace options
}  // namespace CVC4
