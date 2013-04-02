/*********************                                                        */
/*! \file proof.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef __CVC4__PROOF_H
#define __CVC4__PROOF_H

#include <iostream>

namespace CVC4 {

class CVC4_PUBLIC Proof {
public:
  virtual ~Proof() { }
  virtual void toStream(std::ostream& out) = 0;
};/* class Proof */

}/* CVC4 namespace */

#endif /* __CVC4__PROOF_H */
