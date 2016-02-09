/*********************                                                        */
/*! \file theory_sets_rels.cpp
 ** \verbatim
 ** Original author: Paul Meng
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Sets theory implementation.
 **
 ** Extension to Sets theory.
 **/

#include "theory/sets/theory_sets_rels.h"

//#include "expr/emptyset.h"
//#include "options/sets_options.h"
//#include "smt/smt_statistics_registry.h"
//#include "theory/sets/expr_patterns.h" // ONLY included here
//#include "theory/sets/scrutinize.h"
//#include "theory/sets/theory_sets.h"
//#include "theory/theory_model.h"
//#include "util/result.h"


using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace sets {

  TheorySetsRels::TheorySetsRels(eq::EqualityEngine* eq):
    d_eqEngine(eq)
  {
    d_eqEngine->addFunctionKind(kind::PRODUCT);
    d_eqEngine->addFunctionKind(kind::JOIN);
    d_eqEngine->addFunctionKind(kind::TRANSPOSE);
    d_eqEngine->addFunctionKind(kind::TRANSCLOSURE);
  }

  TheorySetsRels::TheorySetsRels::~TheorySetsRels() {}

  void TheorySetsRels::TheorySetsRels::check(Theory::Effort level) {

    Debug("rels") <<  "\nStart iterating equivalence class......\n" << std::endl;

    if (!d_eqEngine->consistent())
      return;
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( d_eqEngine );

    std::map< TypeNode, int > typ_num;
    while( !eqcs_i.isFinished() ){
      TNode r = (*eqcs_i);
      TypeNode tr = r.getType();
      if( typ_num.find( tr )==typ_num.end() ){
        typ_num[tr] = 0;
      }
      typ_num[tr]++;
      bool firstTime = true;
      Debug("rels") << "  " << r;
      Debug("rels") << " : { ";
      eq::EqClassIterator eqc_i = eq::EqClassIterator( r, d_eqEngine );
      while( !eqc_i.isFinished() ){
        TNode n = (*eqc_i);
        if( r!=n ){
          if( firstTime ){
            Debug("rels") << std::endl;
            firstTime = false;
          }
          if (n.getKind() == kind::PRODUCT ||
              n.getKind() == kind::JOIN ||
              n.getKind() == kind::TRANSCLOSURE ||
              n.getKind() == kind::TRANSPOSE) {
            Debug("rels") << "    " << n << std::endl;
          }
        }
        ++eqc_i;
      }
      if( !firstTime ){ Debug("rels") << "  "; }
      Debug("rels") << "}" << std::endl;
      ++eqcs_i;
    }
  }
}
}
}





















