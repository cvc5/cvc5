/*********************                                                        */
/*! \file preprocessing_pass_context.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The preprocessing pass context for passes
 **
 ** The preprocessing pass context for passes.
 **/

#include "preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {

PreprocessingPassContext::PreprocessingPassContext(SmtEngine* smt)
    : d_smt(smt) {}

}  // namespace preprocessing
}  // namespace CVC4
