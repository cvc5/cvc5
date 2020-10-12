/*********************                                                        */
/*! \file model.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Model class
 **/

#include "cvc4_private.h"

#ifndef CVC4__MODEL_H
#define CVC4__MODEL_H

#include <iosfwd>
#include <vector>

#include "expr/expr.h"
#include "util/cardinality.h"
#include "theory/theory_model.h"

namespace CVC4 {
namespace smt {
  
class NodeCommand;
class SmtEngine;
class Model;
class TheoryModel;

std::ostream& operator<<(std::ostream&, const Model&);

class Model {
  friend std::ostream& operator<<(std::ostream&, const Model&);
  friend class SmtEngine;
 public:
  /** construct */
  Model(SmtEngine& smt, TheoryModel * tm);
  /** virtual destructor */
  ~Model() { }
  /** get number of commands to report */
  size_t getNumCommands() const;
  /** get command */
  const NodeCommand* getCommand(size_t i) const;
  /** get the smt engine that this model is hooked up to */
  SmtEngine* getSmtEngine() { return &d_smt; }
  /** get the smt engine (as a pointer-to-const) that this model is hooked up to */
  const SmtEngine* getSmtEngine() const { return &d_smt; }
  /** get the input name (file name, etc.) this model is associated to */
  std::string getInputName() const { return d_inputName; }
  /**
   * Returns true if this model is guaranteed to be a model of the input
   * formula. Notice that when CVC4 answers "unknown", it may have a model
   * available for which this method returns false. In this case, this model is
   * only a candidate solution.
   */
  bool isKnownSat() const { return d_isKnownSat; }
  /** Get the underlying theory model */
  TheoryModel * getTheoryModel();
 protected:
  /** The SmtEngine we're associated with */
  SmtEngine& d_smt;
  /** the input name (file name, etc.) this model is associated to */
  std::string d_inputName;
  /**
   * Flag set to false if the model is associated with an "unknown" response
   * from the solver.
   */
  bool d_isKnownSat;
  /** 
   * Pointer to the theory model
   */
  TheoryModel * d_tmodel;
};/* class Model */

}/* smt namespace */
}/* CVC4 namespace */

#endif  /* CVC4__MODEL_H */
