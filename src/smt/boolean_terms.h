/*********************                                                        */
/*! \file boolean_terms.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#pragma once

#include "expr/attribute.h"
#include "expr/node.h"
#include "util/hash.h"
#include <map>
#include <utility>

namespace CVC4 {
namespace smt {

namespace attr {
  struct BooleanTermAttrTag { };
}/* CVC4::smt::attr namespace */

typedef expr::Attribute<attr::BooleanTermAttrTag, Node> BooleanTermAttr;

class BooleanTermConverter {
  /** The type of the Boolean term conversion variable cache */
  typedef std::hash_map<Node, Node, NodeHashFunction> BooleanTermVarCache;

  /** The type of the Boolean term conversion cache */
  typedef std::hash_map< std::pair<Node, theory::TheoryId>, Node,
                         PairHashFunction< Node, bool,
                                           NodeHashFunction, std::hash<size_t> > > BooleanTermCache;
  /** The type of the Boolean term conversion type cache */
  typedef std::hash_map< std::pair<TypeNode, bool>, TypeNode,
                         PairHashFunction< TypeNode, bool,
                                           TypeNodeHashFunction, std::hash<int> > > BooleanTermTypeCache;
  /** The type of the Boolean term conversion datatype cache */
  typedef std::hash_map<const Datatype*, const Datatype*, DatatypeHashFunction> BooleanTermDatatypeCache;

  /** The SmtEngine to which we're associated */
  SmtEngine& d_smt;

  /** The conversion for "false." */
  Node d_ff;
  /** The conversion for "true." */
  Node d_tt;
  /** The conversion for "false" when in datatypes contexts. */
  Node d_ffDt;
  /** The conversion for "true" when in datatypes contexts. */
  Node d_ttDt;

  /** The cache used during Boolean term variable conversion */
  BooleanTermVarCache d_varCache;
  /** The cache used during Boolean term conversion */
  BooleanTermCache d_termCache;
  /** The cache used during Boolean term type conversion */
  BooleanTermTypeCache d_typeCache;
  /** The cache used during Boolean term datatype conversion */
  BooleanTermDatatypeCache d_datatypeCache;

  Node rewriteAs(TNode in, TypeNode as) throw();

  /**
   * Scan a datatype for and convert as necessary.
   */
  const Datatype& convertDatatype(const Datatype& dt) throw();

  /**
   * Convert a type.
   */
  TypeNode convertType(TypeNode type, bool datatypesContext);

  Node rewriteBooleanTermsRec(TNode n, theory::TheoryId parentTheory, std::map<TNode, Node>& quantBoolVars) throw();

public:

  /**
   * Construct a Boolean-term converter associated to the given
   * SmtEngine.
   */
  BooleanTermConverter(SmtEngine& smt);

  /**
   * Rewrite Boolean terms under a node.  The node itself is not converted
   * if boolParent is true, but its Boolean subterms appearing in a
   * non-Boolean context will be rewritten.
   */
  Node rewriteBooleanTerms(TNode n, bool boolParent = true, bool dtParent = false) throw() {
    std::map<TNode, Node> quantBoolVars;
    Assert(!(boolParent && dtParent));
    return rewriteBooleanTermsRec(n, boolParent ? theory::THEORY_BOOL : (dtParent ? theory::THEORY_DATATYPES : theory::THEORY_BUILTIN), quantBoolVars);
  }

};/* class BooleanTermConverter */

}/* CVC4::smt namespace */
}/* CVC4 namespace */
