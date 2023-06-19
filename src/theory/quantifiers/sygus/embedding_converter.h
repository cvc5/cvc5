/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Class for applying the deep embedding for SyGuS
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EMBEDDING_CONVERTER_H
#define CVC5__THEORY__QUANTIFIERS__EMBEDDING_CONVERTER_H

#include <map>
#include <vector>

#include "expr/attribute.h"
#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class SynthConjecture;
class TermDbSygus;

/**
 * Utility for applying the deep embedding from Section 4 of Reynolds et al CAV
 * 2015.
 */
class EmbeddingConverter : protected EnvObj
{
 public:
  EmbeddingConverter(Env& env, TermDbSygus* tds, SynthConjecture* p);
  ~EmbeddingConverter() {}
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

  /** Is the syntax restricted? */
  bool isSyntaxRestricted() { return d_is_syntax_restricted; }
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
  /**
   * Returns true iff there are syntax restrictions on the
   * functions-to-synthesize of sygus conjecture q.
   */
  static bool hasSyntaxRestrictions(Node q);

 private:
  /** The sygus term database we are using */
  TermDbSygus* d_tds;
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
  void collectTerms(Node n,
                    std::map<TypeNode, std::unordered_set<Node>>& consts);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
