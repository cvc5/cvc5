/*********************                                                        */
/*! \file model.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Model class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__MODEL_H
#define __CVC4__MODEL_H

#include <iostream>
#include <vector>

#include "expr/expr.h"
#include "util/cardinality.h"

namespace CVC4 {

class Command;
class SmtEngine;
class Model;

std::ostream& operator<<(std::ostream&, const Model&);

class Model {
  friend std::ostream& operator<<(std::ostream&, const Model&);
  friend class SmtEngine;

  /** the input name (file name, etc.) this model is associated to */
  std::string d_inputName;

protected:
  /** The SmtEngine we're associated with */
  SmtEngine& d_smt;

  /** construct the base class; users cannot do this, only CVC4 internals */
  Model();

public:
  /** virtual destructor */
  virtual ~Model() { }
  /** get number of commands to report */
  size_t getNumCommands() const;
  /** get command */
  const Command* getCommand(size_t i) const;
  /** get the smt engine that this model is hooked up to */
  SmtEngine* getSmtEngine() { return &d_smt; }
  /** get the smt engine (as a pointer-to-const) that this model is hooked up to */
  const SmtEngine* getSmtEngine() const { return &d_smt; }
  /** get the input name (file name, etc.) this model is associated to */
  std::string getInputName() const { return d_inputName; }

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

#endif  /* __CVC4__MODEL_H */
