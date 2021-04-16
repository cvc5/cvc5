/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Model class.
 */

#include "cvc5_private.h"

#ifndef CVC5__MODEL_H
#define CVC5__MODEL_H

#include <iosfwd>
#include <vector>

#include "expr/node.h"

namespace cvc5 {

class SmtEngine;

namespace theory {
class TheoryModel;
}

namespace smt {

class Model;

std::ostream& operator<<(std::ostream&, const Model&);

/**
 * This is the SMT-level model object, that is responsible for maintaining
 * the necessary information for how to print the model, as well as
 * holding a pointer to the underlying implementation of the theory model.
 *
 * The model declarations maintained by this class are context-independent
 * and should be updated when this model is printed.
 */
class Model {
  friend std::ostream& operator<<(std::ostream&, const Model&);
  friend class ::cvc5::SmtEngine;

 public:
  /** construct */
  Model(theory::TheoryModel* tm);
  /** virtual destructor */
  ~Model() {}
  /** get the input name (file name, etc.) this model is associated to */
  std::string getInputName() const { return d_inputName; }
  /**
   * Returns true if this model is guaranteed to be a model of the input
   * formula. Notice that when cvc5 answers "unknown", it may have a model
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
  //----------------------- model declarations
  /** Clear the current model declarations. */
  void clearModelDeclarations();
  /**
   * Set that tn is a sort that should be printed in the model, when applicable,
   * based on the output language.
   */
  void addDeclarationSort(TypeNode tn);
  /**
   * Set that n is a variable that should be printed in the model, when
   * applicable, based on the output language.
   */
  void addDeclarationTerm(Node n);
  /** get declared sorts */
  const std::vector<TypeNode>& getDeclaredSorts() const;
  /** get declared terms */
  const std::vector<Node>& getDeclaredTerms() const;
  //----------------------- end model declarations
 protected:
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
  /**
   * The list of types to print, generally corresponding to declare-sort
   * commands.
   */
  std::vector<TypeNode> d_declareSorts;
  /**
   * The list of terms to print, is typically one-to-one with declare-fun
   * commands.
   */
  std::vector<Node> d_declareTerms;
};

}  // namespace smt
}  // namespace cvc5

#endif /* CVC5__MODEL_H */
