/*********************                                                        */
/*! \file sygus_grammar_cons.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief class for constructing inductive datatypes that correspond to
 ** grammars that encode syntactic restrictions for SyGuS.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_CONS_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_CONS_H

#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class SynthConjecture;

/** utility for constructing datatypes that correspond to syntactic restrictions,
* and applying the deep embedding from Section 4 of Reynolds et al CAV 2015.
*/
class CegGrammarConstructor
{
public:
 CegGrammarConstructor(QuantifiersEngine* qe, SynthConjecture* p);
 ~CegGrammarConstructor() {}
 /** process
  *
  * This converts node q based on its deep embedding
  * (Section 4 of Reynolds et al CAV 2015).
  * The syntactic restrictions are associated with
  * the functions-to-synthesize using the attribute
  * SygusSynthGrammarAttribute.
  * The arguments templates and template_args
  * indicate templates for the function to synthesize,
  * in particular the solution for the i^th function
  * to synthesis must be of the form
  *   templates[i]{ templates_arg[i] -> t }
  * for some t if !templates[i].isNull().
  */
 Node process(Node q,
              const std::map<Node, Node>& templates,
              const std::map<Node, Node>& templates_arg);
 /**
  * Same as above, but we have already determined that the set of first-order
  * datatype variables that will quantify the deep embedding conjecture are
  * the vector ebvl.
  */
 Node process(Node q,
              const std::map<Node, Node>& templates,
              const std::map<Node, Node>& templates_arg,
              const std::vector<Node>& ebvl);
 /** is the syntax restricted? */
 bool isSyntaxRestricted() { return d_is_syntax_restricted; }
 /** make the default sygus datatype type corresponding to builtin type range
 *   bvl is the set of free variables to include in the grammar
 *   fun is for naming
 *   extra_cons is a set of extra constant symbols to include in the grammar,
 *   exclude_cons is used to exclude operators from the grammar,
 *   term_irrelevant is a set of terms that should not be included in the
 *      grammar.
 *   include_cons is a set of operators that will be included if they are in the default grammar as well (and only them)
 */
 static TypeNode mkSygusDefaultType(
     TypeNode range,
     Node bvl,
     const std::string& fun,
     std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> >& extra_cons,
     std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> >& exclude_cons,
     std::unordered_set<Node, NodeHashFunction>& term_irrelevant,
     const std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>& include_cons = std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>());
 /** make the default sygus datatype type corresponding to builtin type range */
 static TypeNode mkSygusDefaultType(TypeNode range,
                                    Node bvl,
                                    const std::string& fun)
 {
   std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> > extra_cons;
   std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> > exclude_cons;
   std::unordered_set<Node, NodeHashFunction> term_irrelevant;
   return mkSygusDefaultType(
       range, bvl, fun, extra_cons, exclude_cons, term_irrelevant);
  }
  /** make the sygus datatype type that encodes the solution space (lambda
  * templ_arg. templ[templ_arg]) where templ_arg
  * has syntactic restrictions encoded by sygus type templ_arg_sygus_type
  *   bvl is the set of free variables to include in the grammar
  *   fun is for naming
  */
  static TypeNode mkSygusTemplateType( Node templ, Node templ_arg, TypeNode templ_arg_sygus_type, Node bvl, const std::string& fun );
  /**
   * Returns the sygus variable list for function-to-synthesize variable f.
   * These are the names of the arguments of f, which should be included in the
   * grammar for f. This returns either the variable list set explicitly via the
   * attribute SygusSynthFunVarListAttribute, or a fresh variable list of the
   * proper type otherwise. It will return null if f is not a function.
   */
  static Node getSygusVarList(Node f);
  /**
   * Returns true iff there are syntax restrictions on the
   * functions-to-synthesize of sygus conjecture q.
   */
  static bool hasSyntaxRestrictions(Node q);
  /**
   * Make the builtin constants for type "type" that should be included in a
   * sygus grammar, add them to vector ops.
   */
  static void mkSygusConstantsForType(TypeNode type, std::vector<Node>& ops);
  /**
   * Convert node n based on deep embedding, see Section 4 of Reynolds et al
   * CAV 2015.
   *
   * This returns the result of converting n to its deep embedding based on
   * the mapping from functions to datatype variables, stored in
   * d_synth_fun_vars. This method should be called only after calling process
   * above.
   */
  Node convertToEmbedding(Node n);

 private:
  /** reference to quantifier engine */
  QuantifiersEngine * d_qe;
  /** parent conjecture
  * This contains global information about the synthesis conjecture.
  */
  SynthConjecture* d_parent;
  /**
   * Maps each synthesis function to its corresponding (first-order) sygus
   * datatype variable. This map is initialized by the process methods.
   */
  std::map<Node, Node> d_synth_fun_vars;
  /** is the syntax restricted? */
  bool d_is_syntax_restricted;
  /** collect terms */
  void collectTerms( Node n, std::map< TypeNode, std::unordered_set<Node, NodeHashFunction> >& consts );
  //---------------- grammar construction
  // helper for mkSygusDefaultGrammar (makes unresolved type for mutually recursive datatype construction)
  static TypeNode mkUnresolvedType(const std::string& name, std::set<Type>& unres);
  // collect the list of types that depend on type range
  static void collectSygusGrammarTypesFor(TypeNode range,
                                          std::vector<TypeNode>& types);
  /** helper function for function mkSygusDefaultType
  * Collects a set of mutually recursive datatypes "datatypes" corresponding to
  * encoding type "range" to SyGuS.
  *   unres is used for the resulting call to mkMutualDatatypeTypes
  */
  static void mkSygusDefaultGrammar(
      TypeNode range,
      Node bvl,
      const std::string& fun,
      std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> >& extra_cons,
      std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> >& exclude_cons,
      std::unordered_set<Node, NodeHashFunction>& term_irrelevant,
      std::vector<CVC4::Datatype>& datatypes,
      std::set<Type>& unres,
      const std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>& include_cons = std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>());

  // helper function for mkSygusTemplateType
  static TypeNode mkSygusTemplateTypeRec( Node templ, Node templ_arg, TypeNode templ_arg_sygus_type, Node bvl, 
                                          const std::string& fun, unsigned& tcount );
  //---------------- end grammar construction
};

} /* namespace CVC4::theory::quantifiers */
} /* namespace CVC4::theory */
} /* namespace CVC4 */

#endif
