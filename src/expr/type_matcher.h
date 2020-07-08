/*********************                                                        */
/*! \file type_matcher.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A class representing a type matcher
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__TYPE_MATCHER_H
#define CVC4__EXPR__TYPE_MATCHER_H

#include <vector>

#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {

/**
 * This class is used for inferring the parameters of an instantiated
 * parametric datatype. For example, given parameteric datatype:
 *   (par (T) (List T))
 * and instantiated parametric datatype (List Int), this class is used to
 * infer the mapping { T -> Int }.
 */
class TypeMatcher
{
 public:
  TypeMatcher() {}
  /** Initialize this class to do matching with datatype type dt */
  TypeMatcher(TypeNode dt);
  ~TypeMatcher() {}
  /**
   * Add the parameter types from datatype type dt to the above vectors,
   * initializing d_match to null.
   */
  void addTypesFromDatatype(TypeNode dt);
  /**
   * Do matching on type pattern and tn.
   * If this method returns true, then tn is an instantiation of parametric
   * datatype pattern. The parameters of tn that were inferred are stored in
   * d_match such that pattern * { d_types -> d_match } = tn.
   */
  bool doMatching(TypeNode pattern, TypeNode tn);

  /** Get the parameter types that this class matched on */
  void getTypes(std::vector<TypeNode>& types) const;
  /**
   * Get the match for the parameter types based on the last call to doMatching.
   */
  void getMatches(std::vector<TypeNode>& types) const;

 private:
  /** The parameter types */
  std::vector<TypeNode> d_types;
  /** The types they matched */
  std::vector<TypeNode> d_match;
  /** Add a parameter type to the above vectors */
  void addType(TypeNode t);
  /** Add parameter types to the above vectors */
  void addTypes(const std::vector<TypeNode>& types);
}; /* class TypeMatcher */

}  // namespace CVC4

#endif /* CVC4__MATCHER_H */
