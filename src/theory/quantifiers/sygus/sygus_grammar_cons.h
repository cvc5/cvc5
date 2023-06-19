/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Yoni Zohar, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Class for constructing inductive datatypes that correspond to
 * grammars that encode syntactic restrictions for SyGuS.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_CONS_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_CONS_H

#include <map>
#include <vector>

#include "expr/attribute.h"
#include "expr/node.h"
#include "expr/sygus_datatype.h"
#include "options/quantifiers_options.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * Utility for constructing datatypes that correspond to syntactic restrictions.
 */
class CegGrammarConstructor
{
public:
 CegGrammarConstructor() {}
 ~CegGrammarConstructor() {}

 /**
  * Make the default sygus datatype type corresponding to builtin type range
  * arguments:
  *   - bvl: the set of free variables to include in the grammar
  *   - fun: used for naming
  *   - extra_cons: a set of extra constant symbols to include in the grammar,
  *     regardless of their inclusion in the default grammar.
  *   - exclude_cons: used to exclude operators from the grammar,
  *   - term_irrelevant: a set of terms that should not be included in the
  *      grammar.
  *   - include_cons: a set of operators such that if this set is not empty,
  *     its elements that are in the default grammar (and only them)
  *     will be included.
  */
 static TypeNode mkSygusDefaultType(
     const Options& opts,
     TypeNode range,
     Node bvl,
     const std::string& fun,
     std::map<TypeNode, std::unordered_set<Node>>& extra_cons,
     std::map<TypeNode, std::unordered_set<Node>>& exclude_cons,
     std::map<TypeNode, std::unordered_set<Node>>& include_cons,
     std::unordered_set<Node>& term_irrelevant);

 /**
  * Make the default sygus datatype type corresponding to builtin type range.
  */
 static TypeNode mkSygusDefaultType(const Options& opts,
                                    TypeNode range,
                                    Node bvl,
                                    const std::string& fun)
 {
   std::map<TypeNode, std::unordered_set<Node>> extra_cons;
   std::map<TypeNode, std::unordered_set<Node>> exclude_cons;
   std::map<TypeNode, std::unordered_set<Node>> include_cons;
   std::unordered_set<Node> term_irrelevant;
   return mkSygusDefaultType(opts,
                             range,
                             bvl,
                             fun,
                             extra_cons,
                             exclude_cons,
                             include_cons,
                             term_irrelevant);
  }

  /** make the sygus datatype type that encodes the solution space (lambda
  * templ_arg. templ[templ_arg]) where templ_arg
  * has syntactic restrictions encoded by sygus type templ_arg_sygus_type
  *   bvl is the set of free variables to include in the grammar
  *   fun is for naming
  */
  static TypeNode mkSygusTemplateType( Node templ, Node templ_arg, TypeNode templ_arg_sygus_type, Node bvl, const std::string& fun );
  /**
   * Make the builtin constants for type "type" that should be included in a
   * sygus grammar, add them to vector ops.
   */
  static void mkSygusConstantsForType(TypeNode type, std::vector<Node>& ops);
  /** Is it possible to construct a default grammar for type t? */
  static bool isHandledType(TypeNode t);

 private:
  /** A class for generating sygus datatypes */
  class SygusDatatypeGenerator
  {
   public:
    SygusDatatypeGenerator(const std::string& name);
    ~SygusDatatypeGenerator() {}
    /**
     * Possibly add a constructor to d_sdt, based on the criteria mentioned
     * in this class below. For details see expr/sygus_datatype.h.
     */
    void addConstructor(Node op,
                        const std::string& name,
                        const std::vector<TypeNode>& consTypes,
                        int weight = -1);
    /**
     * Possibly add a constructor to d_sdt, based on the criteria mentioned
     * in this class below.
     */
    void addConstructor(Kind k,
                        const std::vector<TypeNode>& consTypes,
                        int weight = -1);
    /** Should we include constructor with operator op? */
    bool shouldInclude(Node op) const;
    /** The constructors that should be excluded. */
    std::unordered_set<Node> d_exclude_cons;
    /**
     * If this set is non-empty, then only include variables and constructors
     * from it.
     */
    std::unordered_set<Node> d_include_cons;
    /** The sygus datatype we are generating. */
    SygusDatatype d_sdt;
  };

  // helper for mkSygusDefaultGrammar (makes unresolved type for mutually recursive datatype construction)
  static TypeNode mkUnresolvedType(const std::string& name);
  // collect the list of types that depend on type range
  static void collectSygusGrammarTypesFor(TypeNode range,
                                          std::vector<TypeNode>& types);
  /** helper function for function mkSygusDefaultType
  * Collects a set of mutually recursive datatypes "datatypes" corresponding to
  * encoding type "range" to SyGuS.
  */
  static void mkSygusDefaultGrammar(
      TypeNode range,
      Node bvl,
      const std::string& fun,
      std::map<TypeNode, std::unordered_set<Node>>& extra_cons,
      std::map<TypeNode, std::unordered_set<Node>>& exclude_cons,
      const std::map<TypeNode, std::unordered_set<Node>>& include_cons,
      std::unordered_set<Node>& term_irrelevant,
      std::vector<SygusDatatypeGenerator>& sdts,
      options::SygusGrammarConsMode sgcm);

  // helper function for mkSygusTemplateType
  static TypeNode mkSygusTemplateTypeRec(Node templ,
                                         Node templ_arg,
                                         TypeNode templ_arg_sygus_type,
                                         Node bvl,
                                         const std::string& fun,
                                         unsigned& tcount);

  /**
   * Given a kind k, create a lambda operator with the given builtin input type
   * and an extra zero argument of that same type.  For example, for k = LEQ and
   * bArgType = Int, the operator will be lambda x : Int. x + 0.  Currently the
   * supported input types are Real (thus also Int) and BitVector.
   */
  static Node createLambdaWithZeroArg(Kind k,
                                      TypeNode bArgType);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
