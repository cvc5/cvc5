/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Liana Hadarean, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Class to encapsulate preregistration duties
 *
 * This class permits the CNF stream implementation to reach into the theory
 * engine to preregister only those terms with an associated SAT literal (at
 * the point when they get the SAT literal), without having to refer to the
 * TheoryEngine class directly.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__REGISTRAR_H
#define CVC5__PROP__REGISTRAR_H

namespace cvc5 {
namespace prop {

class Registrar {
public:
  virtual ~Registrar() {}
  virtual void preRegister(Node n) = 0;

};/* class Registrar */

class NullRegistrar : public Registrar {
public:
 void preRegister(Node n) override {}

};/* class NullRegistrar */

}  // namespace prop
}  // namespace cvc5

#endif /* CVC5__PROP__REGISTRAR_H */
