/*********************                                                        */
/*! \file sexpr.h
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: none
 ** Minor contributors (to current version): taking, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Simple representation of SMT S-expressions.
 **
 ** Simple representation of SMT S-expressions.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__SEXPR_H_
#define __CVC4__SEXPR_H_

#include "util/Assert.h"

#include <vector>
#include <string>

namespace CVC4 {

/**
 * A simple S-expression. An S-expression is either an atom with a string value, or a
 * list of other S-expressions.
 */
class CVC4_PUBLIC SExpr {

  /** Flag telling us if this is an atom or a list. */
  bool d_isAtom;

  /** The value of an atomic S-expression. */
  std::string d_value;

  /** The children of a list S-expression. */
  std::vector<SExpr> d_children;

public:
  SExpr() :
    d_isAtom(true) {
  }

  SExpr(const std::string& value) :
    d_isAtom(true),
    d_value(value) {
  }

  SExpr(const std::vector<SExpr> children) :
    d_isAtom(false),
    d_children(children) {
  }

  /** Is this S-expression an atom? */
  bool isAtom() const;

  /** Get the string value of this S-expression. This will cause an error if this S-expression
   * is not an atom.
   */
  const std::string getValue() const;

  /** Get the children of this S-expression. This will cause an error if this S-expression
   * is not a list.
   */
  const std::vector<SExpr> getChildren() const;
};

inline bool SExpr::isAtom() const {
  return d_isAtom;
}

inline const std::string SExpr::getValue() const {
  AlwaysAssert( d_isAtom );
  return d_value;
}

inline const std::vector<SExpr> SExpr::getChildren() const {
  AlwaysAssert( !d_isAtom );
  return d_children;
}

inline std::ostream& operator<<(std::ostream& out, const SExpr& sexpr) {
  if( sexpr.isAtom() ) {
    out << sexpr.getValue();
  } else {
    std::vector<SExpr> children = sexpr.getChildren();
    out << "(";
    bool first = true;
    for( std::vector<SExpr>::iterator it = children.begin(); it != children.end(); ++it ) {
      if( first ) {
        first = false;
      } else {
        out << " ";
      }
        out << *it;
    }
    out << ")";
  }
  return out;
}

}

#endif /* __CVC4__SEXPR_H_ */
