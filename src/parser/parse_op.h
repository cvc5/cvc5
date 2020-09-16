/*********************                                                        */
/*! \file parse_op.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Definitions of parsed operators.
 **/

#include "cvc4parser_public.h"

#ifndef CVC4__PARSER__PARSE_OP_H
#define CVC4__PARSER__PARSE_OP_H

#include <string>

#include "api/cvc4cpp.h"

namespace CVC4 {

/** A parsed operator
 *
 * The purpose of this struct is to store information regarding a parsed term
 * that might not be ready to associate with an expression.
 *
 * While parsing terms in smt2, we may store a combination of one or more of
 * the following to track how to process this term:
 * (1) A kind.
 * (2) A string name.
 * (3) An expression expr.
 * (4) A type t.
 * (5) An operator object.
 *
 * Examples:
 *
 * - For declared functions f that we have not yet looked up in a symbol table,
 * we store (2). We may store a name in a state if f is overloaded and we have
 * not yet parsed its arguments to know how to disambiguate f.
 * - For tuple selectors (_ tupSel n), we store (1) and (3). Kind is set to
 * APPLY_SELECTOR, and expr is set to n, which is to be interpreted by the
 * caller as the n^th generic tuple selector. We do this since there is no
 * AST expression representing generic tuple select, and we do not have enough
 * type information at this point to know the type of the tuple we will be
 * selecting from.
 * - For array constant specifications prior to type ascription e.g. when we
 * have parsed "const", we store (1), setting the kind to STORE_ALL.
 * - For array constant specifications (as const (Array T1 T2)), we store (1)
 * and (4), where kind is set to STORE_ALL and type is set to (Array T1 T2).
 * When parsing this as an operator e.g. ((as const (Array T1 T2)) t), we
 * interpret this operator by converting the next parsed constant of type T2 to
 * an Array of type (Array T1 T2) over that constant.
 */
struct CVC4_PUBLIC ParseOp
{
  ParseOp(api::Kind k = api::NULL_EXPR) : d_kind(k) {}
  /** The kind associated with the parsed operator, if it exists */
  api::Kind d_kind;
  /** The name associated with the parsed operator, if it exists */
  std::string d_name;
  /** The expression associated with the parsed operator, if it exists */
  api::Term d_expr;
  /** The type associated with the parsed operator, if it exists */
  api::Sort d_type;
  /** The operator associated with the parsed operator, if it exists */
  api::Op d_op;

  /* Return true if this is equal to 'p'. */
  bool operator==(const ParseOp& p) const
  {
    return d_kind == p.d_kind && d_name == p.d_name && d_expr == p.d_expr
           && d_type == p.d_type && d_op == p.d_op;
  }
};

std::ostream& operator<<(std::ostream& os, const ParseOp& p);

}  // namespace CVC4

#endif /* CVC4__PARSER__PARSE_OP_H */
