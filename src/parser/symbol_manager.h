/*********************                                                        */
/*! \file symbol_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The symbol manager
 **/

#include "cvc4parser_public.h"

#ifndef CVC4__PARSER__SYMBOL_MANAGER_H
#define CVC4__PARSER__SYMBOL_MANAGER_H

#include <map>
#include <set>
#include <string>

#include "api/cvc4cpp.h"
#include "expr/symbol_table.h"

namespace CVC4 {
namespace parser {

/**
 * Symbol manager, which manages:
 * (1) The symbol table used by the parser
 * (2) Information related to the (! ... :named s) feature in SMT-LIB version 2,
 *
 */
class CVC4_PUBLIC SymbolManager
{
 public:
  SymbolManager(api::Solver* s);
  ~SymbolManager() {}
  /** Get the underlying symbol table */
  SymbolTable * getSymbolTable();
  //---------------------------- named expressions
  /** Set name of term t to name
   *
   * @param t The term to name
   * @param name The given name
   * @param isAssertion Whether t is being given a name in an assertion
   * context. In particular, this is true if and only if there was an assertion
   * command of the form (assert (! t :named name)).
   * 
   * Notice that assertion names take priority over ordinary names.
   */
  void setName(api::Term t, const std::string& name, bool isAssertion = false);
  /** Get name for term t
   *
   * @param t The term
   * @param name The argument to update with the name of t
   * @param isAssertion Whether we only wish to get the assertion name of t
   * @return true if t has a name. If so, name is updated to that name.
   * Otherwise, name is unchanged.
   */
  bool getName(api::Term t, std::string& name, bool isAssertion = false) const;
  /**
   * Convert list of terms to list of names. This adds to names the names of
   * all terms in ts that has names. Terms that do not have names are not
   * included.
   *
   * @param ts The terms
   * @param names The name list
   * @param areAssertions Whether we only wish to include assertion names
   */
  void getNames(const std::vector<api::Term>& ts,
                std::vector<std::string>& names,
                bool areAssertions = false) const;
  //---------------------------- end named expressions

  /** Bits for use in mkVar() flags. */
  enum
  {
    VAR_FLAG_NONE = 0,
    VAR_FLAG_GLOBAL = 1,
    VAR_FLAG_DEFINED = 2
  };

 private:
  /** The API Solver object. */
  api::Solver* d_solver;
  /**
    * The declaration scope that is "owned" by this symbol manager.
    */
  SymbolTable d_symtabAllocated;
  /** Map terms to names */
  std::map<api::Term, std::string> d_names;
  /** The set of terms with assertion names */
  std::set<api::Term> d_namedAsserts;
};

}  // namespace parser
}  // namespace CVC4

#endif /* CVC4__PARSER__SYMBOL_MANAGER_H */
