/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Definitions of parsed operators.
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__PARSE_OP_H
#define CVC5__PARSER__PARSE_OP_H

#include <cvc5/cvc5.h>

#include <string>
#include <vector>

namespace cvc5 {

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
 *
 * Examples:
 *
 * - For declared functions f that we have not yet looked up in a symbol table,
 * we store (2). We may store a name in a state if f is overloaded and we have
 * not yet parsed its arguments to know how to disambiguate f.
 * - For tuple selectors (_ tuple_select n), we store (1) and (3). Kind is set to
 * APPLY_SELECTOR, and expr is set to n, which is to be interpreted by the
 * caller as the n^th generic tuple selector. We do this since there is no
 * AST expression representing generic tuple select, and we do not have enough
 * type information at this point to know the type of the tuple we will be
 * selecting from.
 * - For array constant specifications (as const (Array T1 T2)), we store (1)
 * and (3), where kind is set to INTERNAL_KIND and expr is set to a placeholder
 * variable of type (Array T1 T2).
 * When parsing this as an operator e.g. ((as const (Array T1 T2)) t), we
 * interpret this operator by converting the next parsed constant of type T2 to
 * an Array of type (Array T1 T2) over that constant.
 */
struct ParseOp
{
  ParseOp(cvc5::Kind k = cvc5::NULL_TERM) : d_kind(k) {}
  /** The kind associated with the parsed operator, if it exists */
  cvc5::Kind d_kind;
  /** The name associated with the parsed operator, if it exists */
  std::string d_name;
  /** The expression associated with the parsed operator, if it exists */
  cvc5::Term d_expr;
  /**
   * The indices if the operator is indexed, but cvc5::Op is the null operator.
   * This is the case for operator symbols that cannot be resolved to a kind
   * without parsing the arguments. This is currently only the case for
   * `to_fp`.
   */
  std::vector<uint32_t> d_indices;

  /* Return true if this is equal to 'p'. */
  bool operator==(const ParseOp& p) const
  {
    return d_kind == p.d_kind && d_name == p.d_name && d_expr == p.d_expr
           && d_indices == p.d_indices;
  }
};

std::ostream& operator<<(std::ostream& os, const ParseOp& p);

}  // namespace cvc5

#endif /* CVC5__PARSER__PARSE_OP_H */
