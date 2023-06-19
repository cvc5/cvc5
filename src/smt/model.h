/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {
namespace smt {

class Model;

std::ostream& operator<<(std::ostream&, const Model&);

/**
 * A utility for representing a model for pretty printing.
 */
class Model {
 public:
  /** Constructor
   * @param isKnownSat True if this model is associated with a "sat" response,
   * or false if it is associated with an "unknown" response.
   */
  Model(bool isKnownSat, const std::string& inputName);
  /** get the input name (file name, etc.) this model is associated to */
  std::string getInputName() const { return d_inputName; }
  /**
   * Returns true if this model is guaranteed to be a model of the input
   * formula. Notice that when cvc5 answers "unknown", it may have a model
   * available for which this method returns false. In this case, this model is
   * only a candidate solution.
   */
  bool isKnownSat() const { return d_isKnownSat; }
  /** Get domain elements */
  const std::vector<Node>& getDomainElements(TypeNode tn) const;
  /** Get value */
  Node getValue(TNode n) const;
  /** Get separation logic heap and nil, return true if they have been set */
  bool getHeapModel(Node& h, Node& nilEq) const;
  //----------------------- model declarations
  /**
   * Set that tn is a sort that should be printed in the model, when applicable,
   * based on the output language.
   *
   * @param tn The uninterpreted sort
   * @param elements The domain elements of tn in the model
   */
  void addDeclarationSort(TypeNode tn, const std::vector<Node>& elements);
  /**
   * Set that n is a variable that should be printed in the model, when
   * applicable, based on the output language.
   *
   * @param n The variable
   * @param value The value of the variable in the model
   */
  void addDeclarationTerm(Node n, Node value);
  /**
   * Set the separation logic model information where h is the heap and nilEq
   * is the value of sep.nil.
   *
   * @param h The value of heap in the heap model
   * @param nilEq The value of sep.nil in the heap model
   */
  void setHeapModel(Node h, Node nilEq);
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
  /** The interpretation of the above sorts, as a list of domain elements. */
  std::map<TypeNode, std::vector<Node>> d_domainElements;
  /**
   * The list of terms to print, is typically one-to-one with declare-fun
   * commands.
   */
  std::vector<Node> d_declareTerms;
  /** Mapping terms to values */
  std::map<Node, Node> d_declareTermValues;
  /** Separation logic heap and nil */
  Node d_sepHeap;
  Node d_sepNilEq;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif /* CVC5__SMT__MODEL_H */
