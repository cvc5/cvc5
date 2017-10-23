/*********************                                                        */
/*! \file sygus_grammar_cons.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of techniqures for static preprocessing and analysis
 *of
 ** sygus conjectures.
 **/
#include "theory/quantifiers/sygus_process_conj.h"

#include <stack>

#include "expr/datatype.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {

CegConjectureProcess::CegConjectureProcess( QuantifiersEngine * qe ) : 
d_qe( qe ){

}

CegConjectureProcess::~CegConjectureProcess() {}

Node CegConjectureProcess::simplify(Node q) { return q; }

void CegConjectureProcess::initialize(Node n, std::vector<Node>& candidates) {
  if (Trace.isOn("ceg-process")) {
    Trace("ceg-process") << "Process conjecture : " << n
                         << " with candidates: " << std::endl;
    for (unsigned i = 0; i < candidates.size(); i++) {
      Trace("ceg-process") << candidates[i] << std::endl;
    }
  }
}

Node CegConjectureProcess::getSymmetryBreakingPredicate(Node x, Node e,
                                                        TypeNode tn,
                                                        unsigned tindex,
                                                        unsigned depth) {
  return Node::null();
}

void CegConjectureProcess::debugPrint( const char * c ) {

}

}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */
