/*********************                                                        */
/*! \file boolean_terms.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/
#include "smt/boolean_terms.h"

#include <algorithm>
#include <map>
#include <set>
#include <stack>
#include <string>

#include "expr/kind.h"
#include "expr/node_manager_attributes.h"
#include "options/boolean_term_conversion_mode.h"
#include "options/booleans_options.h"
#include "smt/smt_engine.h"
#include "theory/theory_engine.h"
#include "theory/theory_model.h"
#include "util/ntuple.h"

using namespace std;
using namespace CVC4::theory;
using namespace CVC4::theory::booleans;

namespace CVC4 {
namespace smt {

}/* CVC4::smt namespace */
}/* CVC4 namespace */
