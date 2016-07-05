/*********************                                                        */
/*! \file proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef __CVC4__PROOF_H
#define __CVC4__PROOF_H

#include <iosfwd>
#include <ext/hash_map>

namespace CVC4 {

class Expr;
class ProofLetCount;
struct ExprHashFunction;

typedef __gnu_cxx::hash_map<Expr, ProofLetCount, ExprHashFunction> ProofLetMap;

class CVC4_PUBLIC Proof {
public:
  virtual ~Proof() { }
  virtual void toStream(std::ostream& out) = 0;
  virtual void toStream(std::ostream& out, const ProofLetMap& map) = 0;
};/* class Proof */

}/* CVC4 namespace */

#endif /* __CVC4__PROOF_H */
