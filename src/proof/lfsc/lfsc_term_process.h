/*********************                                                        */
/*! \file lfsc_term_process.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing Lfsc proof nodes
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF__LFSC__LFSC_TERM_PROCESS_H
#define CVC4__PROOF__LFSC__LFSC_TERM_PROCESS_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/type_node.h"
#include "proof/term_processor.h"

namespace CVC4 {
namespace proof {

class LfscTermProcessor : public TermProcessor
{
 public:
  LfscTermProcessor();
  ~LfscTermProcessor() {}
  /** convert to internal */
  Node runConvert(Node n) override;
  /** convert to internal */
  TypeNode runConvertType(TypeNode tn) override;

 private:
  /** Get symbol for term */
  Node getSymbolInternalFor(Node n, const std::string& name, uint32_t v = 0);
  /** Get symbol internal */
  Node getSymbolInternal(Kind k,
                         TypeNode tn,
                         const std::string& name,
                         uint32_t v = 0);
  /** terms with different syntax than smt2 */
  std::map<std::tuple<Kind, TypeNode, uint32_t>, Node> d_symbols;
  /** arrow type constructor */
  TypeNode d_arrow;
  /** the type of LFSC sorts, which can appear in terms */
  TypeNode d_sortType;
};

}  // namespace proof
}  // namespace CVC4

#endif
