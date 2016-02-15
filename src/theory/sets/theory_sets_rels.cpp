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

#include "expr/datatype.h"
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

  TheorySetsRels::TheorySetsRels(context::Context* c,
                                 context::UserContext* u,
                                 eq::EqualityEngine* eq):
    d_trueNode(NodeManager::currentNM()->mkConst<bool>(true)),
    d_falseNode(NodeManager::currentNM()->mkConst<bool>(false)),
    d_eqEngine(eq),
    d_relsSaver(c)
  {
    d_eqEngine->addFunctionKind(kind::PRODUCT);
    d_eqEngine->addFunctionKind(kind::JOIN);
    d_eqEngine->addFunctionKind(kind::TRANSPOSE);
    d_eqEngine->addFunctionKind(kind::TRANSCLOSURE);
  }

  TheorySetsRels::~TheorySetsRels() {}

  void TheorySetsRels::check(Theory::Effort level) {

    Debug("rels-eqc") <<  "\nStart iterating equivalence classes......\n" << std::endl;

    if (!d_eqEngine->consistent())
      return;
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( d_eqEngine );

    while( !eqcs_i.isFinished() ){
      TNode r = (*eqcs_i);
      bool firstTime = true;
      Debug("rels-eqc") << "  " << r;
      Debug("rels-eqc") << " : { ";
      eq::EqClassIterator eqc_i = eq::EqClassIterator( r, d_eqEngine );
      while( !eqc_i.isFinished() ){
        TNode n = (*eqc_i);

        // only consider membership constraints that involving relatioinal operators
        if((d_eqEngine->getRepresentative(r) == d_eqEngine->getRepresentative(d_trueNode)
              || d_eqEngine->getRepresentative(r) == d_eqEngine->getRepresentative(d_falseNode))
            && !d_relsSaver.contains(n)) {
          d_relsSaver.insert(n);

          // case: (b, a) IS_IN (TRANSPOSE X)
          //    => (a, b) IS_IN X
          if(n.getKind() == kind::MEMBER) {
            if(kind::TRANSPOSE == n[1].getKind()) {
              Node reversedTuple = reverseTuple(n[0]);
              Node fact = NodeManager::currentNM()->mkNode(kind::MEMBER, reversedTuple, n[1][0]);
//              assertMembership(fact, n, r == d_trueNode);
            } else if(kind::JOIN == n[1].getKind()) {

            }else if(kind::PRODUCT == n[1].getKind()) {

            }
          }
        }

        if( r!=n ){
          if( firstTime ){
            Debug("rels-eqc") << std::endl;
            firstTime = false;
          }
          if (n.getKind() == kind::PRODUCT ||
              n.getKind() == kind::JOIN ||
              n.getKind() == kind::TRANSCLOSURE ||
              n.getKind() == kind::TRANSPOSE) {
            Debug("rels-eqc") << "    *** " << n << std::endl;
          }else{
            Debug("rels-eqc") << "    " << n <<std::endl;
          }
        }
        ++eqc_i;
      }
      if( !firstTime ){ Debug("rels-eqc") << "  "; }
      Debug("rels-eqc") << "}" << std::endl;
      ++eqcs_i;
    }
  }

  Node TheorySetsRels::reverseTuple(TNode tuple) {
    // need to register the newly created tuple?
    Assert(tuple.getType().isDatatype());

    std::vector<Node> elements;
    Datatype dt = (Datatype)((tuple.getType()).getDatatype());

    elements.push_back(tuple.getOperator());
    for(Node::iterator child_it = tuple.end()-1;
              child_it != tuple.begin()-1; --child_it) {
      elements.push_back(*child_it);
    }
    return NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, elements);
  }

  void TheorySetsRels::assertMembership(TNode fact, TNode reason, bool polarity) {
    TNode explain = reason;
    if(!polarity) {
      explain = reason.negate();
    }
    Debug("rels") << " polarity : " << polarity << " reason: " << explain << std::endl;
    d_eqEngine->assertPredicate(fact, polarity, explain);
  }
}
}
}














