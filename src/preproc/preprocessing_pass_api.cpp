/*********************                                                        */
/*! \file preprocessing_pass_api.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation for preprocessing pass api for passes
 **
 ** Implementation for preprocessing pass api for passes. Takes in variables and
 *methods from d_smt
 *and d_private and allows for access to the passes.
 **/
#include "preprocessing_pass_api.h"

namespace CVC4 {
namespace preproc {

PreprocessingPassAPI::PreprocessingPassAPI(SmtEngine* smt) : d_smt(smt) {}

}  // namespace preproc
}  // namespace CVC4
