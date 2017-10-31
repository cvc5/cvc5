/*********************                                                        */
/*! \file theory_model.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Clark Barrett, Morgan Deters, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Model class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__THEORY_MODEL_BUILDER_H
#define __CVC4__THEORY__THEORY_MODEL_BUILDER_H

#include <unordered_map>
#include <unordered_set>

#include "theory/theory_model.h"

namespace CVC4 {
namespace theory {

/** TheoryEngineModelBuilder class
 * 
 * This is the model builder class used by TheoryEngine
 * for constructing TheoryModel objects. The call to
 * TheoryEngineModelBuilder::buildModel(...) is made after full
 * effort check passes with no theory solvers adding
 * lemmas or conflicts, and theory combination passes
 * with no splits on shared terms.
 */
class TheoryEngineModelBuilder : public ModelBuilder
{
  typedef std::unordered_map<Node, Node, NodeHashFunction> NodeMap;
  typedef std::unordered_set<Node, NodeHashFunction> NodeSet;
public:
  TheoryEngineModelBuilder(TheoryEngine* te);
  virtual ~TheoryEngineModelBuilder(){}
  /** Build model function.
   * 
   * Should be called only on TheoryModels m.
   * This constructs the model m, via the following steps:
   * (1) call TheoryEngine::collectModelInfo, 
   * (2) builder-specified pre-processing,
   * (3) determine equivalence classes of m's
   *     equality engine that initially contain constants,
   * (4) assign constants to all equivalence classes
   *     of m's equality engine, through alternating
   *     iterations of evaluation and enumeration,
   * (5) builder-specific post-processing.
   * 
   * This function returns false if any of the above
   * steps results in a lemma is sent on an output channel.
   * Lemmas may be sent on an output channel by this
   * builder in steps (2) or (5), for instance, if the model we 
   * are building fails to satisfy a quantified formula.
   */
  virtual bool buildModel(Model* m) override;
  /** Debug check model.
   * 
   * This throws an assertion failure if the model 
   * contains an equivalence class with two terms t1 and t2
   * such that t1^M != t2^M.
   */
  void debugCheckModel(Model* m);
protected:
  /** pointer to theory engine */
  TheoryEngine* d_te;
  //-----------------------------------virtual functions 
  /** pre-process build model 
   * Called in step (2) of the build construction,
   * described above.
   */
  virtual bool preProcessBuildModel(TheoryModel* m);
  /** process build model 
   * Called in step (5) of the build construction,
   * described above.
   */
  virtual bool processBuildModel(TheoryModel* m);
  /** debug the model
   * Check assertions and printing debug information for the model. 
   */
  virtual void debugModel( TheoryModel* m ) {}
  //-----------------------------------end virtual functions 
  /** normalize representative */
  Node normalize(TheoryModel* m, TNode r, bool evalOnly);
  bool isAssignable(TNode n);
  void checkTerms(TNode n, TheoryModel* tm, NodeSet& cache);
  void assignConstantRep( TheoryModel* tm, Node eqc, Node const_rep );
  void addToTypeList( TypeNode tn, std::vector< TypeNode >& type_list, std::map< TypeNode, bool >& visiting );
  /** is v an excluded codatatype value */
  bool isExcludedCdtValue( Node v, std::set<Node>* repSet, std::map< Node, Node >& assertedReps, Node eqc );
  bool isCdtValueMatch( Node v, Node r, Node eqc, Node& eqc_m );
  /** does type tn involve an uninterpreted sort? */
  bool involvesUSort( TypeNode tn );
  bool isExcludedUSortValue( std::map< TypeNode, unsigned >& eqc_usort_count, Node v, std::map< Node, bool >& visited );
  /** assign function f based on the model m. 
  * This construction is based on "table form". For example:
  * (f 0 1) = 1
  * (f 0 2) = 2
  * (f 1 1) = 3
  * ...
  * becomes:
  * f = (lambda xy. (ite (and (= x 0) (= y 1)) 1 
  *                 (ite (and (= x 0) (= y 2)) 2
  *                 (ite (and (= x 1) (= y 1)) 3 ...)))
  */
  void assignFunction(TheoryModel* m, Node f);
  /** assign function f based on the model m. 
  * This construction is based on "dag form". For example:
  * (f 0 1) = 1
  * (f 0 2) = 2
  * (f 1 1) = 3
  * ...
  * becomes:
  * f = (lambda xy. (ite (= x 0) (ite (= y 1) 1
  *                              (ite (= y 2) 2 ...))
  *                 (ite (= x 1) (ite (= y 1) 3 ...)
  *                              ...))
  * 
  * where the above is represented as a directed acyclic graph (dag).
  * This construction is accomplished by assigning values to (f c) 
  * terms before f, e.g. 
  * (f 0) = (lambda y. (ite (= y 1) 1
  *                    (ite (= y 2) 2 ...))
  * (f 1) = (lambda y. (ite (= y 1) 3 ...))
  * where
  * f = (lambda xy. (ite (= x 0) ((f 0) y)
  *                 (ite (= x 1) ((f 1) y) ...))
  */
  void assignHoFunction(TheoryModel* m, Node f);
  /** Assign all unassigned functions in the model m (those returned by TheoryModel::getFunctionsToAssign), 
  * using the two functions above. Currently:
  * If ufHo is disabled, we call assignFunction for all functions. 
  * If ufHo is enabled, we call assignHoFunction.
  */
  void assignFunctions(TheoryModel* m);
private:
  /** normalized cache 
   * The normalized form of a node f(t1...tn) is :
   *   TODO
   */
  NodeMap d_normalizedCache;
  /** mapping from terms to the constant associated with their equivalence class */
  std::map< Node, Node > d_constantReps;
};/* class TheoryEngineModelBuilder */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__THEORY_MODEL_BUILDER_H */
