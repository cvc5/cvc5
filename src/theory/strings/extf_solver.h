/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Solver for extended functions of theory of strings.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__EXTF_SOLVER_H
#define CVC5__THEORY__STRINGS__EXTF_SOLVER_H

#include <map>
#include <vector>

#include "context/cdo.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/ext_theory.h"
#include "theory/strings/base_solver.h"
#include "theory/strings/core_solver.h"
#include "theory/strings/inference_manager.h"
#include "theory/strings/sequences_stats.h"
#include "theory/strings/skolem_cache.h"
#include "theory/strings/solver_state.h"
#include "theory/strings/strings_rewriter.h"
#include "theory/strings/theory_strings_preprocess.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

/**
 * Non-static information about an extended function t. This information is
 * constructed and used during the check extended function evaluation
 * inference schema.
 *
 * In the following, we refer to the "context-dependent simplified form"
 * of a term t to be the result of rewriting t * sigma, where sigma is a
 * derivable substitution in the current context. For example, the
 * context-depdendent simplified form of contains( x++y, "a" ) given
 * sigma = { x -> "" } is contains(y,"a").
 */
class ExtfInfoTmp
{
 public:
  ExtfInfoTmp() : d_modelActive(true) {}
  /**
   * If s is in d_ctn[true] (resp. d_ctn[false]), then contains( t, s )
   * (resp. ~contains( t, s )) holds in the current context. The vector
   * d_ctnFrom is the explanation for why this holds. For example,
   * if d_ctn[false][i] is "A", then d_ctnFrom[false][i] might be
   * t = x ++ y AND x = "" AND y = "B".
   */
  std::map<bool, std::vector<Node> > d_ctn;
  std::map<bool, std::vector<Node> > d_ctnFrom;
  /**
   * The constant that t is entailed to be equal to, or null if none exist.
   */
  Node d_const;
  /**
   * The explanation for why t is equal to its context-dependent simplified
   * form.
   */
  std::vector<Node> d_exp;
  /** This flag is false if t is reduced in the model. */
  bool d_modelActive;
};

/**
 * Extended function solver for the theory of strings. This manages extended
 * functions for the theory of strings using a combination of context-dependent
 * simplification (Reynolds et al CAV 2017) and lazy reductions.
 */
class ExtfSolver : protected EnvObj
{
  typedef context::CDHashSet<Node> NodeSet;

 public:
  ExtfSolver(Env& env,
             SolverState& s,
             InferenceManager& im,
             TermRegistry& tr,
             StringsRewriter& rewriter,
             BaseSolver& bs,
             CoreSolver& cs,
             ExtTheory& et,
             SequencesStatistics& statistics);
  ~ExtfSolver();
  /** check extended functions evaluation
   *
   * This applies "context-dependent simplification" for all active extended
   * function terms in this SAT context. This infers facts of the form:
   *   x = c => f( t1 ... tn ) = c'
   * where the rewritten form of f( t1...tn ) { x |-> c } is c', and x = c
   * is a (tuple of) equalities that are asserted in this SAT context, and
   * f( t1 ... tn ) is a term from this SAT context.
   *
   * For more details, this is steps 4 when effort=0 and step 6 when
   * effort=1 from Strategy 1 in Reynolds et al, "Scaling up DPLL(T) String
   * Solvers using Context-Dependent Simplification", CAV 2017. When called with
   * effort=3, we apply context-dependent simplification based on model values.
   */
  void checkExtfEval(int effort);
  /** check extended function reductions
   *
   * This adds "reduction" lemmas for each active extended function in this SAT
   * context. These are generally lemmas of the form:
   *   F[t1...tn,k] ^ f( t1 ... tn ) = k
   * where f( t1 ... tn ) is an active extended function, k is a fresh constant
   * and F is a formula that constrains k based on the definition of f.
   *
   * For more details, this is step 7 from Strategy 1 in Reynolds et al,
   * CAV 2017. We stratify this in practice based on the effort level,
   * where for instance, we reduce negatively asserted str.contains only
   * at LAST_CALL effort. For more information see discussion of "model-based
   * reductions" in Reynolds et al CAV 2022.
   */
  void checkExtfReductions(Theory::Effort e);
  /**
   * Check for extended functions that should be applied eagerly. This is
   * called earlier in the search strategy of strings, in particular before
   * the core equality reasoning is done.
   */
  void checkExtfReductionsEager();
  /** get preprocess module */
  StringsPreprocess* getPreprocess() { return &d_preproc; }

  /**
   * Get the current substitution for term n.
   *
   * This method returns a term that n is currently equal to in the current
   * context. It updates exp to contain an explanation of why it is currently
   * equal to that term.
   *
   * The argument effort determines what kind of term to return, either
   * a constant in the equivalence class of n (effort=0), the normal form of
   * n (effort=1,2) or the model value of n (effort>=3). The latter is only
   * valid at LAST_CALL effort. If a term of the above form cannot be returned,
   * then n itself is returned.
   */
  Node getCurrentSubstitutionFor(int effort, Node n, std::vector<Node>& exp);
  /** get mapping from extended functions to their information
   *
   * This information is valid during a full effort check after a call to
   * checkExtfEval.
   */
  const std::map<Node, ExtfInfoTmp>& getInfo() const;
  //---------------------------------- information about ExtTheory
  /** Are there any active extended functions? */
  bool hasExtendedFunctions() const;
  /**
   * Get the function applications of kind k that are active in the current
   * context (see ExtTheory::getActive).
   */
  std::vector<Node> getActive(Kind k) const;
  /**
   * Return true if n is active in the model. If this method returns false,
   * then n is already satisfied in the model (its value in the model is
   * the same as its representative in the equality engine).
   */
  bool isActiveInModel(Node n) const;
  /**
   * @return The relevant active terms. This method retrieves the relevant
   * terms from the term registry and filters out inactive terms.
   *
   * Note that the set of active terms is not a subset of the relevant terms
   * since active terms may include preregistered terms that don't appear
   * in any current assertions.
   */
  std::vector<Node> getRelevantActive() const;
  //---------------------------------- end information about ExtTheory
  /**
   * Print the relevant information regarding why we have a model, return as a
   * string.
   */
  std::string debugPrintModel();

  /**
   * Is extended function (or regular expression membership) reduced? Note that
   * if n has Boolean type, our reductions are dependent upon the polarity of n,
   * in which case n may be the negation of an extended function. For
   * example, (not (str.in_re x R)) indicates that we have reduced
   * (str.in_re x R) based on its negative unfolding.
   */
  bool isReduced(const Node& n) const;
  /**
   * Mark that extended function (or regular expression membership) n has been
   * reduced. Like above, n could be a negation of an extended function of
   * Boolean type.
   */
  void markReduced(const Node& n);

 private:
  /**
   * Helper method for checkExtfReductions / maybeHasCandidateModel, returns
   * true if a reduction lemma was sent if doSend = true, or would have been
   * sent if doSend = false.
   */
  bool checkExtfReductionsInternal(int effort, bool doSend);
  /**
   * Determines if n should be reduced based on the effort level.
   *
   * @param effort the effort level
   * @param n the term to reduce
   * @param pol polarity of n, where 1 true, -1 false, 0 neither
   */
  bool shouldDoReduction(int effort, Node n, int pol);
  /** do reduction
   *
   * This is called when an extended function application n is not able to be
   * simplified by context-depdendent simplification, and we are resorting to
   * expanding n to its full semantics via a reduction. This method returns
   * true if it successfully reduced n by some reduction. If so, it either
   * caches that the reduction lemma was sent, or marks n as reduced in this
   * SAT-context. The argument effort has the same meaning as in
   * checkExtfReductions.
   *
   * @param n the term to reduce
   * @param pol polarity of n, where 1 true, -1 false, 0 neither
   */
  void doReduction(Node n, int pol);
  /** check extended function inferences
   *
   * This function makes additional inferences for n that do not contribute
   * to its reduction, but may help show a refutation.
   *
   * This function is called when the context-depdendent simplified form of
   * n is nr. The argument "in" is the information object for n. The argument
   * "effort" has the same meaning as the effort argument of checkExtfEval.
   */
  void checkExtfInference(Node n, Node nr, ExtfInfoTmp& in, int effort);
  /** The solver state object */
  SolverState& d_state;
  /** The (custom) output channel of the theory of strings */
  InferenceManager& d_im;
  /** Reference to the term registry of theory of strings */
  TermRegistry& d_termReg;
  /** The theory rewriter for this theory. */
  StringsRewriter& d_rewriter;
  /** reference to the base solver, used for certain queries */
  BaseSolver& d_bsolver;
  /** reference to the core solver, used for certain queries */
  CoreSolver& d_csolver;
  /** the extended theory object for the theory of strings */
  ExtTheory& d_extt;
  /** Reference to the statistics for the theory of strings/sequences. */
  SequencesStatistics& d_statistics;
  /** preprocessing utility, for performing strings reductions */
  StringsPreprocess d_preproc;
  /** Common constants */
  Node d_true;
  Node d_false;
  /** Empty vector */
  std::vector<Node> d_emptyVec;
  /** map extended functions to the above information */
  std::map<Node, ExtfInfoTmp> d_extfInfoTmp;
  /** any non-reduced extended functions exist? */
  context::CDO<bool> d_hasExtf;
  /** extended functions inferences cache */
  NodeSet d_extfInferCache;
  /** The set of extended functions we have sent reduction lemmas for */
  NodeSet d_reduced;
};

/** An extended theory callback */
class StringsExtfCallback : public ExtTheoryCallback
{
 public:
  StringsExtfCallback() : d_esolver(nullptr) {}
  /**
   * Get current substitution based on the underlying extended function
   * solver.
   */
  bool getCurrentSubstitution(int effort,
                              const std::vector<Node>& vars,
                              std::vector<Node>& subs,
                              std::map<Node, std::vector<Node> >& exp) override;
  /** The extended function solver */
  ExtfSolver* d_esolver;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__EXTF_SOLVER_H */
