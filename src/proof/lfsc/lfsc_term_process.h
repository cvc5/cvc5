/*********************                                                        */
/*! \file lfsc_term_process.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing Lfsc proof nodes
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF__LFSC__LFSC_TERM_PROCESS_H
#define CVC4__PROOF__LFSC__LFSC_TERM_PROCESS_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/type_node.h"
#include "proof/lfsc/term_processor.h"

namespace CVC4 {
namespace proof {

class LfscTermProcessCallback : public TermProcessCallback
{
 public:
  LfscTermProcessCallback();
  ~LfscTermProcessCallback() {}
  /** convert to internal */
  Node convertInternal(Node n) override;
  /** convert to internal */
  TypeNode convertInternalType(TypeNode tn) override;

 private:
  //--------------------------- terms with different syntax than smt2
  /** Empty string */
  //--------------------------- terms with different syntax than smt2
};

}  // namespace proof
}  // namespace CVC4

#endif
