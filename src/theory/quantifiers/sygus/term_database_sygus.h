/*********************                                                        */
/*! \file term_database_sygus.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief term database sygus class
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_SYGUS_H
#define CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_SYGUS_H

#include <unordered_set>

#include "expr/dtype.h"
#include "theory/evaluator.h"
#include "theory/quantifiers/extended_rewrite.h"
#include "theory/quantifiers/fun_def_evaluator.h"
#include "theory/quantifiers/sygus/sygus_eval_unfold.h"
#include "theory/quantifiers/sygus/sygus_explain.h"
#include "theory/quantifiers/sygus/type_info.h"
#include "theory/quantifiers/term_database.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class SynthConjecture;

/** role for registering an enumerator */
enum EnumeratorRole
{
  /** The enumerator populates a pool of terms (e.g. for PBE). */
  ROLE_ENUM_POOL,
  /** The enumerator is the single solution of the problem. */
  ROLE_ENUM_SINGLE_SOLUTION,
  /**
   * The enumerator is part of the solution of the problem (e.g. multiple
   * functions to synthesize).
   */
  ROLE_ENUM_MULTI_SOLUTION,
  /** The enumerator must satisfy some set of constraints */
  ROLE_ENUM_CONSTRAINED,
};
std::ostream& operator<<(std::ostream& os, EnumeratorRole r);

// TODO :issue #1235 split and document this class
class TermDbSygus {
 public:
  TermDbSygus(context::Context* c, QuantifiersEngine* qe);
  ~TermDbSygus() {}
  /** Reset this utility */
  bool reset(Theory::Effort e);
  /** Identify this utility */
  std::string identify() const { return "TermDbSygus"; }
  /** register the sygus type
   *
   * This initializes this database for sygus datatype type tn. This may
   * throw an assertion failure if the sygus grammar has type errors. Otherwise,
   * after registering a sygus type, the query function getTypeInfo can be
   * called for tn.
   *
   * This method returns true if tn is a sygus datatype type and false
   * otherwise.
   */
  bool registerSygusType(TypeNode tn);

  //------------------------------utilities
  /** get the explanation utility */
  SygusExplain* getExplain() { return d_syexp.get(); }
  /** get the extended rewrite utility */
  ExtendedRewriter* getExtRewriter() { return d_ext_rw.get(); }
  /** get the evaluator */
  Evaluator* getEvaluator() { return d_eval.get(); }
  /** (recursive) function evaluator utility */
  FunDefEvaluator* getFunDefEvaluator() { return d_funDefEval.get(); }
  /** evaluation unfolding utility */
  SygusEvalUnfold* getEvalUnfold() { return d_eval_unfold.get(); }
  //------------------------------end utilities

  //------------------------------enumerators
  /**
   * Register a variable e that we will do enumerative search on.
   *
   * conj : the conjecture that the enumeration of e is for.
   *
   * f : the synth-fun that the enumeration of e is for.Notice that enumerator
   * e may not be one-to-one with f in synthesis-through-unification approaches
   * (e.g. decision tree construction for PBE synthesis).
   *
   * erole : the role of this enumerator (see definition of EnumeratorRole).
   * Depending on this and the policy for actively-generated enumerators
   * (--sygus-active-gen), the enumerator may be "actively-generated".
   * For example, if --sygus-active-gen=var-agnostic, then the enumerator will
   * only generate values whose variables are in canonical order (only x1-x2
   * and not x2-x1 will be generated, assuming x1 and x2 are in the same
   * "subclass", see getSubclassForVar).
   *
   * An "active guard" may be allocated by this method for e based on erole
   * and the policies for active generation.
   */
  void registerEnumerator(Node e,
                          Node f,
                          SynthConjecture* conj,
                          EnumeratorRole erole);
  /** is e an enumerator registered with this class? */
  bool isEnumerator(Node e) const;
  /** return the conjecture e is associated with */
  SynthConjecture* getConjectureForEnumerator(Node e) const;
  /** return the function-to-synthesize e is associated with */
  Node getSynthFunForEnumerator(Node e) const;
  /** get active guard for e */
  Node getActiveGuardForEnumerator(Node e) const;
  /** are we using symbolic constructors for enumerator e? */
  bool usingSymbolicConsForEnumerator(Node e) const;
  /** is this enumerator agnostic to variables? */
  bool isVariableAgnosticEnumerator(Node e) const;
  /** is this enumerator a "basic" enumerator.
   *
   * A basic enumerator is one that does not rely on the sygus extension of the
   * datatypes solver. Basic enumerators enumerate all concrete terms for their
   * type for a single abstract value.
   */
  bool isBasicEnumerator(Node e) const;
  /** is this a "passively-generated" enumerator?
   *
   * A "passively-generated" enumerator is one for which the terms it enumerates
   * are obtained by looking at its model value only. For passively-generated
   * enumerators, it is the responsibility of the user of that enumerator (say
   * a SygusModule) to block the current model value of it before asking for
   * another value. By default, the Cegis module uses passively-generated
   * enumerators and "conjecture-specific refinement" to rule out models
   * for passively-generated enumerators.
   *
   * On the other hand, an "actively-generated" enumerator is one for which the
   * terms it enumerates are not necessarily a subset of the model values the
   * enumerator takes. Actively-generated enumerators are centrally managed by
   * SynthConjecture. The user of actively-generated enumerators are prohibited
   * from influencing its model value. For example, conjecture-specific
   * refinement in Cegis is not applied to actively-generated enumerators.
   */
  bool isPassiveEnumerator(Node e) const;
  /** get all registered enumerators */
  void getEnumerators(std::vector<Node>& mts);
  /** Register symmetry breaking lemma
   *
   * This function registers lem as a symmetry breaking lemma template for
   * subterms of enumerator e. For more information on symmetry breaking
   * lemma templates, see datatypes/datatypes_sygus.h.
   *
   * tn : the (sygus datatype) type that lem applies to, i.e. the
   * type of terms that lem blocks models for,
   * sz : the minimum size of terms that the lem blocks,
   * isTempl : if this flag is false, then lem is a (concrete) lemma.
   * If this flag is true, then lem is a symmetry breaking lemma template
   * over x, where x is returned by the call to getFreeVar( tn, 0 ).
   */
  void registerSymBreakLemma(
      Node e, Node lem, TypeNode tn, unsigned sz, bool isTempl = true);
  /** Has symmetry breaking lemmas been added for any enumerator? */
  bool hasSymBreakLemmas(std::vector<Node>& enums) const;
  /** Get symmetry breaking lemmas
   *
   * Returns the set of symmetry breaking lemmas that have been registered
   * for enumerator e. It adds these to lemmas.
   */
  void getSymBreakLemmas(Node e, std::vector<Node>& lemmas) const;
  /** Get the type of term symmetry breaking lemma lem applies to */
  TypeNode getTypeForSymBreakLemma(Node lem) const;
  /** Get the minimum size of terms symmetry breaking lemma lem applies to */
  unsigned getSizeForSymBreakLemma(Node lem) const;
  /** Returns true if lem is a lemma template, false if lem is a lemma */
  bool isSymBreakLemmaTemplate(Node lem) const;
  /** Clear information about symmetry breaking lemmas for enumerator e */
  void clearSymBreakLemmas(Node e);
  //------------------------------end enumerators

  //-----------------------------conversion from sygus to builtin
  /** get free variable
   *
   * This class caches a list of free variables for each type, which are
   * used, for instance, for constructing canonical forms of terms with free
   * variables. This function returns the i^th free variable for type tn.
   * If useSygusType is true, then this function returns a variable of the
   * analog type for sygus type tn (see d_fv for details).
   */
  TNode getFreeVar(TypeNode tn, int i, bool useSygusType = false);
  /** get free variable and increment
   *
   * This function returns the next free variable for type tn, and increments
   * the counter in var_count for that type.
   */
  TNode getFreeVarInc(TypeNode tn,
                      std::map<TypeNode, int>& var_count,
                      bool useSygusType = false);
  /** returns true if n is a cached free variable (in d_fv). */
  bool isFreeVar(Node n) const;
  /** returns the identifier for a cached free variable. */
  size_t getFreeVarId(Node n) const;
  /** returns true if n has a cached free variable (in d_fv). */
  bool hasFreeVar(Node n);
  /** get sygus proxy variable
   *
   * Returns a fresh variable of type tn with the SygusPrintProxyAttribute set
   * to constant c. The type tn should be a sygus datatype type, and the type of
   * c should be the analog type of tn. The semantics of the returned node
   * is "the variable of sygus datatype tn that encodes constant c".
   */
  Node getProxyVariable(TypeNode tn, Node c);
  /** make generic
   *
   * This function returns a builtin term f( t1, ..., tn ) where f is the
   * builtin op of the sygus datatype constructor specified by arguments
   * dt and c. The mapping pre maps child indices to the term for that index
   * in the term we are constructing. That is, for each i = 1,...,n:
   *   If i is in the domain of pre, then ti = pre[i].
   *   If i is not in the domain of pre, then ti = d_fv[1][ var_count[Ti ] ],
   *     and var_count[Ti] is incremented.
   * If doBetaRed is true, then lambda operators are eagerly eliminated via
   * beta reduction.
   */
  Node mkGeneric(const DType& dt,
                 unsigned c,
                 std::map<TypeNode, int>& var_count,
                 std::map<int, Node>& pre,
                 bool doBetaRed = true);
  /** same as above, but with empty var_count */
  Node mkGeneric(const DType& dt,
                 int c,
                 std::map<int, Node>& pre,
                 bool doBetaRed = true);
  /** same as above, but with empty pre */
  Node mkGeneric(const DType& dt, int c, bool doBetaRed = true);
  /** makes a symbolic term concrete
   *
   * Given a sygus datatype term n of type tn with holes (symbolic constructor
   * applications), this function returns a term in which holes are replaced by
   * unique variables. To track counters for introducing unique variables, we
   * use the var_count map.
   */
  Node canonizeBuiltin(Node n);
  Node canonizeBuiltin(Node n, std::map<TypeNode, int>& var_count);
  /** sygus to builtin
   *
   * Given a sygus datatype term n of type tn, this function returns its analog,
   * that is, the term that n encodes.
   */
  Node sygusToBuiltin(Node n, TypeNode tn);
  /** same as above, but without tn */
  Node sygusToBuiltin(Node n) { return sygusToBuiltin(n, n.getType()); }
  /** evaluate builtin
   *
   * bn is a term of some sygus datatype tn. This function returns the rewritten
   * form of bn [ args / vars(tn) ], where vars(tn) is the sygus variable
   * list for type tn (see Datatype::getSygusVarList).
   *
   * If the argument tryEval is true, we consult the evaluator before the
   * rewriter, for performance reasons.
   */
  Node evaluateBuiltin(TypeNode tn,
                       Node bn,
                       const std::vector<Node>& args,
                       bool tryEval = true);
  /** evaluate with unfolding
   *
   * n is any term that may involve sygus evaluation functions. This function
   * returns the result of unfolding the evaluation functions within n and
   * rewriting the result. For example, if eval_A is the evaluation function
   * for the datatype:
   *   A -> C_0 | C_1 | C_x | C_+( C_A, C_A )
   * corresponding to grammar:
   *   A -> 0 | 1 | x | A + A
   * then calling this function on eval( C_+( x, 1 ), 4 ) = y returns 5 = y.
   * The node returned by this function is in (extended) rewritten form.
   */
  Node evaluateWithUnfolding(Node n);
  /** same as above, but with a cache of visited nodes */
  Node evaluateWithUnfolding(
      Node n, std::unordered_map<Node, Node, NodeHashFunction>& visited);
  /** is evaluation point?
   *
   * Returns true if n is of the form eval( x, c1...cn ) for some variable x
   * and constants c1...cn.
   */
  bool isEvaluationPoint(Node n) const;
  /** return the builtin type of tn
   *
   * The type tn should be a sygus datatype type that has been registered to
   * this database.
   */
  TypeNode sygusToBuiltinType(TypeNode tn);
  //-----------------------------end conversion from sygus to builtin
  /**
   * Get type information about sygus datatype type tn. The type tn should be
   * (a subfield type of) a type that has been registered to this class.
   */
  SygusTypeInfo& getTypeInfo(TypeNode tn);
  /**
   * Rewrite the given node using the utilities in this class. This may
   * involve (recursive function) evaluation.
   */
  Node rewriteNode(Node n) const;

  /** print to sygus stream n on trace c */
  static void toStreamSygus(const char* c, Node n);

 private:
  /** reference to the quantifiers engine */
  QuantifiersEngine* d_quantEngine;

  //------------------------------utilities
  /** sygus explanation */
  std::unique_ptr<SygusExplain> d_syexp;
  /** extended rewriter */
  std::unique_ptr<ExtendedRewriter> d_ext_rw;
  /** evaluator */
  std::unique_ptr<Evaluator> d_eval;
  /** (recursive) function evaluator utility */
  std::unique_ptr<FunDefEvaluator> d_funDefEval;
  /** evaluation function unfolding utility */
  std::unique_ptr<SygusEvalUnfold> d_eval_unfold;
  //------------------------------end utilities

  //------------------------------enumerators
  /** mapping from enumerator terms to the conjecture they are associated with
   */
  std::map<Node, SynthConjecture*> d_enum_to_conjecture;
  /** mapping from enumerator terms to the function-to-synthesize they are
   * associated with 
   */
  std::map<Node, Node> d_enum_to_synth_fun;
  /** mapping from enumerator terms to the guard they are associated with
   * The guard G for an enumerator e has the semantics
   *   if G is true, then there are more values of e to enumerate".
   */
  std::map<Node, Node> d_enum_to_active_guard;
  /**
   * Mapping from enumerators to whether we allow symbolic constructors to
   * appear as subterms of them.
   */
  std::map<Node, bool> d_enum_to_using_sym_cons;
  /** mapping from enumerators to symmetry breaking clauses for them */
  std::map<Node, std::vector<Node> > d_enum_to_sb_lemmas;
  /** mapping from symmetry breaking lemmas to type */
  std::map<Node, TypeNode> d_sb_lemma_to_type;
  /** mapping from symmetry breaking lemmas to size */
  std::map<Node, unsigned> d_sb_lemma_to_size;
  /** mapping from symmetry breaking lemmas to whether they are templates */
  std::map<Node, bool> d_sb_lemma_to_isTempl;
  /** enumerators to whether they are actively-generated */
  std::map<Node, bool> d_enum_active_gen;
  /** enumerators to whether they are variable agnostic */
  std::map<Node, bool> d_enum_var_agnostic;
  /** enumerators to whether they are basic */
  std::map<Node, bool> d_enum_basic;
  //------------------------------end enumerators

  //-----------------------------conversion from sygus to builtin
  /** a cache of fresh variables for each type
   *
   * We store two versions of this list:
   *   index 0: mapping from builtin types to fresh variables of that type,
   *   index 1: mapping from sygus types to fresh varaibles of the type they
   *            encode.
   */
  std::map<TypeNode, std::vector<Node> > d_fv[2];
  /** Maps free variables to the domain type they are associated with in d_fv */
  std::map<Node, TypeNode> d_fv_stype;
  /** Id count for free variables terms */
  std::map<TypeNode, size_t> d_fvTypeIdCounter;
  /**
   * Maps free variables to a unique identifier for their builtin type. Notice
   * that, e.g. free variables of type Int and those that are of a sygus
   * datatype type that encodes Int must have unique identifiers. This is
   * to ensure that sygusToBuiltin for non-ground terms maps variables to
   * unique variabales.
   */
  std::map<Node, size_t> d_fvId;
  /** recursive helper for hasFreeVar, visited stores nodes we have visited. */
  bool hasFreeVar(Node n, std::map<Node, bool>& visited);
  /** cache of getProxyVariable */
  std::map<TypeNode, std::map<Node, Node> > d_proxy_vars;
  //-----------------------------end conversion from sygus to builtin
  // TODO :issue #1235 : below here needs refactor
 public:
  Node d_true;
  Node d_false;

 private:
  /** computes the map d_min_type_depth */
  void computeMinTypeDepthInternal( TypeNode root_tn, TypeNode tn, unsigned type_depth );
  bool involvesDivByZero( Node n, std::map< Node, bool >& visited );

 private:
  /**
   * Maps types that we have called registerSygusType to a flag indicating
   * whether that type is a sygus datatype type. Sygus datatype types that
   * are in this map have initialized type information stored in the map below.
   */
  std::map<TypeNode, bool> d_registerStatus;
  /**
   * The type information for each sygus datatype type that has been registered
   * to this class.
   */
  std::map<TypeNode, SygusTypeInfo> d_tinfo;
  /** a cache for getSelectorWeight */
  std::map<TypeNode, std::map<Node, unsigned> > d_sel_weight;

 public:  // general sygus utilities
  bool isRegistered(TypeNode tn) const;
  /** get the weight of the selector, where tn is the domain of sel */
  unsigned getSelectorWeight(TypeNode tn, Node sel);
  /** get arg type */
  TypeNode getArgType(const DTypeConstructor& c, unsigned i) const;
  /** Do constructors c1 and c2 have the same type? */
  bool isTypeMatch(const DTypeConstructor& c1, const DTypeConstructor& c2);
  /** return whether n is an application of a symbolic constructor */
  bool isSymbolicConsApp(Node n) const;
  /** can construct kind
   *
   * Given a sygus datatype type tn, if this method returns true, then there
   * exists values of tn whose builtin analog is equivalent to
   * <k>( t1, ..., tn ). The sygus types of t1...tn are added to arg_types.
   *
   * For example, if:
   *   A -> A+A | ite( B, A, A ) | x | 1 | 0
   *   B -> and( B, B ) | not( B ) | or( B, B ) | A = A
   * - canConstructKind( A, +, ... ) returns true and adds {A,A} to arg_types,
   * - canConstructKind( B, not, ... ) returns true and adds { B } to arg types.
   *
   * We also may infer that operator is constructable. For example,
   * - canConstructKind( B, ite, ... ) may return true, adding { B, B, B } to
   * arg_types, noting that the term
   *   (and (or (not b1) b2) (or b1 b3)) is equivalent to (ite b1 b2 b3)
   * The argument aggr is whether we use aggressive techniques like the one
   * above to infer a kind is constructable. If this flag is false, we only
   * check if the kind is literally a constructor of the grammar.
   */
  bool canConstructKind(TypeNode tn,
                        Kind k,
                        std::vector<TypeNode>& argts,
                        bool aggr = false);

  Node getSygusNormalized( Node n, std::map< TypeNode, int >& var_count, std::map< Node, Node >& subs );
  Node getNormalized(TypeNode t, Node prog);
  unsigned getSygusTermSize( Node n );
  /** involves div-by-zero */
  bool involvesDivByZero( Node n );
  /** get anchor */
  static Node getAnchor( Node n );
  static unsigned getAnchorDepth( Node n );

};

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_H */
