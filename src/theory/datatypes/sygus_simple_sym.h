/*********************                                                        */
/*! \file sygus_simple_sym.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Simple symmetry breaking for sygus.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DATATYPES__SIMPLE_SYM_BREAK_H
#define __CVC4__THEORY__DATATYPES__SIMPLE_SYM_BREAK_H

#include <map>
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"

namespace CVC4 {
namespace theory {
namespace datatypes {

/** SygusSimpleSymBreak
 *
 * This class implements queries that can be queried statically about sygus
 * grammars, for example, concerning which constructors need not appear at
 * argument positions of others. This is used by the sygus extension of the
 * quantifier-free datatypes procedure for adding symmetry breaking lemmas.
 * We call this class of techniques "simple static symmetry breaking".
 */
class SygusSimpleSymBreak
{
 public:
  SygusSimpleSymBreak(QuantifiersEngine* qe);
  ~SygusSimpleSymBreak() {}
  bool considerArgKind(TypeNode tn, TypeNode tnp, Kind k, Kind pk, int arg);
  bool considerConst(TypeNode tn, TypeNode tnp, Node c, Kind pk, int arg);
  bool considerConst(
      const Datatype& pdt, TypeNode tnp, Node c, Kind pk, int arg);
  int solveForArgument(TypeNode tnp, unsigned cindex, unsigned arg);

 private:
  /** Pointer to the sygus term database */
  quantifiers::TermDbSygus* d_tds;
  /** Pointer to the quantifiers term utility */
  quantifiers::TermUtil* d_tutil;
  /** return the index of the first argument position of c that has type tn */
  int getFirstArgOccurrence(const DatatypeConstructor& c, TypeNode tn);
};

}  // namespace datatypes
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__DATATYPES__SIMPLE_SYM_BREAK_H */
