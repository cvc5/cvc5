/*********************                                                        */
/*! \file util_model.h
 ** \verbatim
 ** Original author: barrett
 ** Major contributors: mdeters
 ** Minor contributors (to current version): ajreynol
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Model class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__UTIL_MODEL_H
#define __CVC4__UTIL_MODEL_H

#include <iostream>
#include <vector>

#include "expr/expr.h"
#include "util/cardinality.h"

namespace CVC4 {

class Command;
class SmtEngine;
class Model;

std::ostream& operator<<(std::ostream&, Model&);

class Model {
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
  virtual Expr getValue(Expr expr) const = 0;
  /** get cardinality for sort */
  virtual Cardinality getCardinality(Type t) const = 0;
};/* class Model */

class ModelBuilder {
public:
  ModelBuilder() { }
  virtual ~ModelBuilder() { }
  virtual void buildModel(Model* m, bool fullModel) = 0;
};/* class ModelBuilder */

}/* CVC4 namespace */

#endif  /* __CVC4__UTIL_MODEL_H */
