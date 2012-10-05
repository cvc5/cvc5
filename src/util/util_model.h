/*********************                                                        */
/*! \file model.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
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
#include <vector>

#include "expr/expr.h"
#include "util/cardinality.h"

namespace CVC4 {

class CVC4_PUBLIC Command;
class CVC4_PUBLIC SmtEngine;
class CVC4_PUBLIC Model;

std::ostream& operator<<(std::ostream&, Model&) CVC4_PUBLIC;

class CVC4_PUBLIC Model {
  friend std::ostream& operator<<(std::ostream&, Model&);

protected:
  /** The SmtEngine we're associated to */
  const SmtEngine& d_smt;

  /** construct the base class; users cannot do this, only CVC4 internals */
  Model();

public:
  /** virtual destructor */
  virtual ~Model() { }
  /** get number of commands to report */
  size_t getNumCommands() const;
  /** get command */
  const Command* getCommand(size_t i) const;
public:
  /** get value for expression */
  virtual Expr getValue(Expr expr) = 0;
  /** get cardinality for sort */
  virtual Cardinality getCardinality(Type t) = 0;
};/* class Model */

class ModelBuilder
{
public:
  ModelBuilder(){}
  virtual ~ModelBuilder(){}
  virtual void buildModel( Model* m, bool fullModel ) = 0;
};/* class ModelBuilder */

}/* CVC4 namespace */

#endif  /* __CVC4__MODEL_H */
