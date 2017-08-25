/*********************                                                        */
/*! \file preprocessing_pass_api.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass api for passes
 **
 ** Preprocessing pass api for passes. Takes in variables and methods from d_smt
 ** and d_private and allows for access to the passes.
 **/
#include "cvc4_private.h"

#ifndef __CVC4__PREPROC__PREPROCESSING_PASS_API_H
#define __CVC4__PREPROC__PREPROCESSING_PASS_API_H

#include <string>
#include "decision/decision_engine.h"
#include "smt/smt_engine.h"
#include "theory/arith/pseudoboolean_proc.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace preproc {

class PreprocessingPassAPI {
 public:
  PreprocessingPassAPI(SmtEngine* smt);
  SmtEngine* getSmt() { return d_smt; }

 private:
  /* SmtEngine that is used to get varialbes */
  SmtEngine* d_smt;
};  // class PreprocessingPassAPI

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__PREPROCESSING_PASS_API_H */
