/*********************                                                        */
/*! \file model.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Model class
 **/

#include "cvc4_public.h"

#ifndef __CVC4__MODEL_H
#define __CVC4__MODEL_H

#include <iostream>

namespace CVC4 {

class Model
{
public:
  virtual void toStream(std::ostream& out) = 0;
};/* class Model */

class ModelBuilder
{
public:
  ModelBuilder(){}
  virtual ~ModelBuilder(){}
  virtual void buildModel( Model* m ) = 0;
};/* class ModelBuilder */

}/* CVC4 namespace */

#endif  /* __CVC4__MODEL_H */
