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
#include "theory/theory_model.h"
#include "util/cardinality.h"

namespace CVC4 {

class SmtEngine;
class NodeCommand;

namespace smt {

class Model;

std::ostream& operator<<(std::ostream&, const Model&);

/**
 * This is the SMT-level model object, that is responsible for maintaining
 * the necessary information for how to print the model, as well as
 * holding a pointer to the underlying implementation of the theory model.
 */
class Model {
  friend std::ostream& operator<<(std::ostream&, const Model&);
  friend class ::CVC4::SmtEngine;

 public:
  /** construct */
  Model(SmtEngine& smt, theory::TheoryModel* tm);
  /** virtual destructor */
  ~Model() {}
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
  theory::TheoryModel* getTheoryModel();
  /** Get the underlying theory model (const version) */
  const theory::TheoryModel* getTheoryModel() const;
  //----------------------- helper methods in the underlying theory model
  /** Is the node n a model core symbol? */
  bool isModelCoreSymbol(TNode sym) const;
  /** Get value */
  Node getValue(TNode n) const;
  /** Does this model have approximations? */
  bool hasApproximations() const;
  //----------------------- end helper methods
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
   * Pointer to the underlying theory model, which maintains all data regarding
   * the values of sorts and terms.
   */
  theory::TheoryModel* d_tmodel;
};

}  // namespace smt
}/* CVC4 namespace */

#endif  /* CVC4__MODEL_H */
