/*********************                                                        */
/*! \file ext_theory.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Extended theory interface.
 **
 ** This implements a generic module, used by theory solvers, for performing
 ** "context-dependent simplification", as described in Reynolds et al
 ** "Designing Theory Solvers with Extensions", FroCoS 2017.
 **
 ** At a high level, this technique implements a generic inference scheme based
 ** on the combination of SAT-context-dependent equality reasoning and
 ** SAT-context-indepedent rewriting.
 **
 ** As a simple example, say
 ** (1) TheoryStrings tells us that the following facts hold in the SAT context:
 **     x = "A" ^ str.contains( str.++( x, z ), "B" ) = true.
 ** (2) The Rewriter tells us that:
 **     str.contains( str.++( "A", z ), "B" ) ----> str.contains( z, "B" ).
 ** From this, this class may infer that the following lemma is T-valid:
 **   x = "A" ^ str.contains( str.++( x, z ), "B" ) => str.contains( z, "B" )
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__EXT_THEORY_H
#define CVC4__THEORY__EXT_THEORY_H

#include <map>
#include <set>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/context.h"
#include "expr/node.h"
#include "theory/theory.h"

namespace CVC4 {
namespace theory {

/**
 * A callback class for ExtTheory below. This class is responsible for
 * determining how to apply context-dependent simplification.
 */
class ExtTheoryCallback
{
 public:
  virtual ~ExtTheoryCallback() {}
  /*
   * Get current substitution at an effort
   * @param effort The effort identifier
   * @param vars The variables to get a substitution for
   * @param subs The terms to substitute for variables, in order. This vector
   * should be updated to one the same size as vars.
   * @param exp The map containing the explanation for each variable. Together
   * with subs, we have that:
   *   ( exp[vars[i]] => vars[i] = subs[i] ) holds for all i
   * @return true if any (non-identity) substitution was added to subs.
   */
  virtual bool getCurrentSubstitution(int effort,
                                      const std::vector<Node>& vars,
                                      std::vector<Node>& subs,
                                      std::map<Node, std::vector<Node> >& exp);

  /*
   * Is extended function n reduced? This returns true if n is reduced to a
   * form that requires no further interaction from the theory.
   *
   * @param effort The effort identifier
   * @param n The term to reduce
   * @param on The original form of n, before substitution
   * @param exp The explanation of on = n
   * @return true if n is reduced.
   */
  virtual bool isExtfReduced(int effort,
                             Node n,
                             Node on,
                             std::vector<Node>& exp);

  /**
   * Get reduction for node n.
   * If return value is true, then n is reduced.
   * If satDep is updated to false, then n is reduced independent of the
   * SAT context (e.g. by a lemma that persists at this
   * user-context level).
   * If nr is non-null, then ( n = nr ) should be added as a lemma by caller,
   * and return value of this method should be true.
   */
  virtual bool getReduction(int effort, Node n, Node& nr, bool& satDep);
};

/** Extended theory class
 *
 * This class is used for constructing generic extensions to theory solvers.
 * In particular, it provides methods for "context-dependent simplification"
 * and "model-based refinement". For details, see Reynolds et al "Design
 * Theory Solvers with Extensions", FroCoS 2017.
 *
 * It maintains:
 * (1) A set of "extended function" kinds (d_extf_kind),
 * (2) A database of active/inactive extended function terms (d_ext_func_terms)
 * that have been registered to the class.
 *
 * This class has methods doInferences/doReductions, which send out lemmas
 * based on the current set of active extended function terms. The former
 * is based on context-dependent simplification, where this class asks the
 * underlying theory for a "derivable substitution", whereby extended functions
 * may be reducable.
 */
class ExtTheory
{
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  /** constructor
   *
   * If cacheEnabled is false, we do not cache results of getSubstitutedTerm.
   */
  ExtTheory(ExtTheoryCallback& p,
            context::Context* c,
            context::UserContext* u,
            OutputChannel& out,
            bool cacheEnabled = false);
  virtual ~ExtTheory() {}
  /** Tells this class to treat terms with Kind k as extended functions */
  void addFunctionKind(Kind k) { d_extf_kind[k] = true; }
  /** Is kind k treated as an extended function by this class? */
  bool hasFunctionKind(Kind k) const
  {
    return d_extf_kind.find(k) != d_extf_kind.end();
  }
  /** register term
   *
   * Registers term n with this class. Adds n to the set of extended function
   * terms known by this class (d_ext_func_terms) if n is an extended function,
   * that is, if addFunctionKind( n.getKind() ) was called.
   */
  void registerTerm(Node n);
  /** register all subterms of n with this class */
  void registerTermRec(Node n);
  /** set n as reduced/inactive
   *
   * If satDep = false, then n remains inactive in the duration of this
   * user-context level
   */
  void markReduced(Node n, bool satDep = true);
  /**
   * Mark that a and b are congruent terms. This sets b inactive, and sets a to
   * inactive if b was inactive.
   */
  void markCongruent(Node a, Node b);
  /** getSubstitutedTerms
   *
   *  input : effort, terms
   *  output : sterms, exp, where ( exp[i] => terms[i] = sterms[i] ) for all i.
   *
   * For each i, sterms[i] = term[i] * sigma for some "derivable substitution"
   * sigma. We obtain derivable substitutions and their explanations via calls
   * to the underlying theory's Theory::getCurrentSubstitution method. This
   * also
   *
   * If useCache is true, we cache the result in d_gst_cache. This is a context
   * independent cache that can be cleared using clearCache() below.
   */
  void getSubstitutedTerms(int effort,
                           const std::vector<Node>& terms,
                           std::vector<Node>& sterms,
                           std::vector<std::vector<Node> >& exp,
                           bool useCache = false);
  /**
   * Same as above, but for a single term. We return the substituted form of
   * term and add its explanation to exp.
   */
  Node getSubstitutedTerm(int effort,
                          Node term,
                          std::vector<Node>& exp,
                          bool useCache = false);
  /** clear the cache for getSubstitutedTerm */
  void clearCache();
  /** doInferences
   *
   * This function performs "context-dependent simplification". The method takes
   * as input:
   *  effort: an identifier used to determine which terms we reduce and the
   *          form of the derivable substitution we will use,
   *  terms: the set of terms to simplify,
   *  batch: if this flag is true, we send lemmas for all terms; if it is false
   *         we send a lemma for the first applicable term.
   *
   * Sends rewriting lemmas of the form ( exp => t = c ) where t is in terms
   * and c is a constant, c = rewrite( t*sigma ) where exp |= sigma. These
   * lemmas are determined by asking the underlying theory for a derivable
   * substitution (through getCurrentSubstitution with getSubstitutedTerm)
   * above, applying this substitution to terms in terms, rewriting
   * the result and checking with the theory whether the resulting term is
   * in reduced form (isExtfReduced).
   *
   * This method adds the extended terms that are still active to nred, and
   * returns true if and only if a lemma of the above form was sent.
   */
  bool doInferences(int effort,
                    const std::vector<Node>& terms,
                    std::vector<Node>& nred,
                    bool batch = true);
  /**
   * Calls the above function, where terms is getActive(), the set of currently
   * active terms.
   */
  bool doInferences(int effort, std::vector<Node>& nred, bool batch = true);
  /** doReductions
   *
   * This method has the same interface as doInferences. In contrast to
   * doInfereces, this method will send reduction lemmas of the form ( t = t' )
   * where t is in terms and t' is an equivalent reduced term.
   */
  bool doReductions(int effort,
                    const std::vector<Node>& terms,
                    std::vector<Node>& nred,
                    bool batch = true);
  bool doReductions(int effort, std::vector<Node>& nred, bool batch = true);

  /** get the set of all extended function terms from d_ext_func_terms */
  void getTerms(std::vector<Node>& terms);
  /** is there at least one active extended function term? */
  bool hasActiveTerm() const;
  /** is n an active extended function term? */
  bool isActive(Node n) const;
  /** get the set of active terms from d_ext_func_terms */
  std::vector<Node> getActive() const;
  /** get the set of active terms from d_ext_func_terms of kind k */
  std::vector<Node> getActive(Kind k) const;

 private:
  /** returns the set of variable subterms of n */
  static std::vector<Node> collectVars(Node n);
  /** is n context dependent inactive? */
  bool isContextIndependentInactive(Node n) const;
  /** do inferences internal */
  bool doInferencesInternal(int effort,
                            const std::vector<Node>& terms,
                            std::vector<Node>& nred,
                            bool batch,
                            bool isRed);
  /** send lemma on the output channel */
  bool sendLemma(Node lem, bool preprocess = false);
  /** reference to the callback */
  ExtTheoryCallback& d_parent;
  /** Reference to the output channel we are using */
  OutputChannel& d_out;
  /** the true node */
  Node d_true;
  /** extended function terms, map to whether they are active */
  NodeBoolMap d_ext_func_terms;
  /**
   * The set of terms from d_ext_func_terms that are SAT-context-independent
   * inactive. For instance, a term t is SAT-context-independent inactive if
   * a reduction lemma of the form t = t' was added in this user-context level.
   */
  NodeSet d_ci_inactive;
  /**
   * Watched term for checking if any non-reduced extended functions exist.
   * This is an arbitrary active member of d_ext_func_terms.
   */
  context::CDO<Node> d_has_extf;
  /** the set of kinds we are treated as extended functions */
  std::map<Kind, bool> d_extf_kind;
  /** information for each term in d_ext_func_terms */
  class ExtfInfo
  {
   public:
    /** all variables in this term */
    std::vector<Node> d_vars;
  };
  std::map<Node, ExtfInfo> d_extf_info;

  // cache of all lemmas sent
  NodeSet d_lemmas;
  NodeSet d_pp_lemmas;
  /** whether we enable caching for getSubstitutedTerm */
  bool d_cacheEnabled;
  /** Substituted term info */
  class SubsTermInfo
  {
   public:
    /** the substituted term */
    Node d_sterm;
    /** an explanation */
    std::vector<Node> d_exp;
  };
  /**
   * This maps an (effort, term) to the information above. It is used as a
   * cache for getSubstitutedTerm when d_cacheEnabled is true.
   */
  std::map<int, std::map<Node, SubsTermInfo> > d_gst_cache;
};

} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* CVC4__THEORY__EXT_THEORY_H */
