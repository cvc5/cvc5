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

#ifndef CVC5__SMT__MODEL_H
#define CVC5__SMT__MODEL_H

#include <iosfwd>
#include <vector>

#include "expr/node.h"

namespace cvc5 {
namespace smt {

class Model;

std::ostream& operator<<(std::ostream&, const Model&);

/**
 * A utility for representing a model for pretty printing.
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
  //----------------------- helper methods in the underlying theory model
  /** Get domain elements */
  const std::vector<Node>& getDomainElements(TypeNode tn) const;
  /** Get value */
  Node getValue(TNode n) const;
  //----------------------- end helper methods
  //----------------------- model declarations
  /** Clear the current model declarations. */
  void clearModelDeclarations();
  /**
   * Set that tn is a sort that should be printed in the model, when applicable,
   * based on the output language.
   */
  void addDeclarationSort(TypeNode tn, const std::vector<Node>& elements);
  /**
   * Set that n is a variable that should be printed in the model, when
   * applicable, based on the output language.
   */
  void addDeclarationTerm(Node n, Node value);
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
   * The list of types to print, generally corresponding to declare-sort
   * commands.
   */
  std::vector<TypeNode> d_declareSorts;
  /**
   * The interpretation of the above sorts
   */
  std::map<TypeNode, std::vector<Node>> d_domainElements;
  /**
   * The list of terms to print, is typically one-to-one with declare-fun
   * commands.
   */
  std::vector<Node> d_declareTerms;
  /** Mapping terms to values */
  std::map<Node, Node> d_declareTermValues;
};

}  // namespace smt
}  // namespace cvc5

#endif /* CVC5__SMT__MODEL_H */
