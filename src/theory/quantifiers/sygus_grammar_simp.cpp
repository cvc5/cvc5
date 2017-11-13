/*********************                                                        */
/*! \file sygus_grammar_cons.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief implementation of class for for simplifying SyGuS grammars after they
 ** are encoded into datatypes.
 **/

#include "theory/quantifiers/sygus_grammar_simp.h"

#include <stack>

#include "expr/datatype.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/ce_guided_conjecture.h"
#include "theory/quantifiers/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusGrammarSimplifier::SygusGrammarSimplifier(QuantifiersEngine* qe,
                                             CegConjecture* p)
    : d_qe(qe), d_parent(p), d_is_syntax_restricted(false), d_has_ite(true)
{
}

TypeNode SygusGrammarSimplifier::normalizeSygusType(TypeNode tn)
{
  const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
  Trace("sygus-grammar-normalize")
    << "Normalizing type " << tn << ", from datatype\n"
    << dt << std::endl;
  return tn;
}


}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */
