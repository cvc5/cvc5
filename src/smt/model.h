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

namespace CVC4 {

class NodeCommand;
class SmtEngine;
class Model;

std::ostream& operator<<(std::ostream&, const Model&);

class Model {
  friend std::ostream& operator<<(std::ostream&, const Model&);
  friend class SmtEngine;

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
  //--------------------------- model cores
  /** set using model core
   *
   * This sets that this model is minimized to be a "model core" for some
   * formula (typically the input formula).
   *
   * For example, given formula ( a>5 OR b>5 ) AND f( c ) = 0,
   * a model for this formula is: a -> 6, b -> 0, c -> 0, f -> lambda x. 0.
   * A "model core" is a subset of this model that suffices to show the
   * above formula is true, for example { a -> 6, f -> lambda x. 0 } is a
   * model core for this formula.
   */
  virtual void setUsingModelCore() = 0;
  /** record model core symbol
   *
   * This marks that sym is a "model core symbol". In other words, its value is
   * critical to the satisfiability of the formula this model is for.
   */
  virtual void recordModelCoreSymbol(Expr sym) = 0;
  /** Check whether this expr is in the model core */
  virtual bool isModelCoreSymbol(Expr expr) const = 0;
  //--------------------------- end model cores
  /** get value for expression */
  virtual Expr getValue(Expr expr) const = 0;
  /** get cardinality for sort */
  virtual Cardinality getCardinality(Type t) const = 0;
  /** print comments */
  virtual void getComments(std::ostream& out) const {}
  /** get heap model (for separation logic) */
  virtual bool getHeapModel( Expr& h, Expr& ne ) const { return false; }
  /** are there any approximations in this model? */
  virtual bool hasApproximations() const { return false; }
  /** get the list of approximations
   *
   * This is a list of pairs of the form (t,p), where t is a term and p
   * is a predicate over t that indicates a property that t satisfies.
   */
  virtual std::vector<std::pair<Expr, Expr> > getApproximations() const = 0;
  /** get the domain elements for uninterpreted sort t
   *
   * This method gets the interpretation of an uninterpreted sort t.
   * All models interpret uninterpreted sorts t as finite sets
   * of domain elements v_1, ..., v_n. This method returns this list for t in
   * this model.
   */
  virtual std::vector<Expr> getDomainElements(Type t) const = 0;

 protected:
  /** the input name (file name, etc.) this model is associated to */
  std::string d_inputName;
  /**
   * Flag set to false if the model is associated with an "unknown" response
   * from the solver.
   */
  bool d_isKnownSat;
};/* class Model */

}/* CVC4 namespace */

#endif  /* CVC4__MODEL_H */
