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
 ** Implementation for preprocessing pass Context for passes. 
 ** Stores a pointer to the SMTEngine that is was created in
 ** and exposes parts of the solver to the preprocessing passes.
 **/
#include "preprocessing_pass_context.h"

namespace CVC4 {
namespace preproc {

PreprocessingPassContext::PreprocessingPassContext(SmtEngine* smt) : d_smt(smt) {}

}  // namespace preproc
}  // namespace CVC4
