/*********************                                                        */
/*! \file theory_uf_candidate generator.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory datatypes candidate generator
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_DATATYPES_CANDIDATE_GENERATOR_H
#define __CVC4__THEORY_DATATYPES_CANDIDATE_GENERATOR_H

#include "theory/quantifiers_engine.h"
#include "theory/datatypes/theory_datatypes.h"
#include "theory/rr_inst_match.h"

namespace CVC4 {
namespace theory {
namespace datatypes {

namespace rrinst {
typedef CVC4::theory::rrinst::CandidateGenerator CandidateGenerator;

// Just iterate amoung the equivalence class of the given node
// node::Null() *can't* be given to reset
class CandidateGeneratorTheoryClass : public CandidateGenerator{
private:
  //instantiator pointer
  TheoryDatatypes* d_th;
  //the equality class iterator
  TheoryDatatypes::EqListN::const_iterator d_eqc_i;
  TheoryDatatypes::EqListN* d_eqc;
public:
  CandidateGeneratorTheoryClass( TheoryDatatypes* th): d_th( th ), d_eqc(NULL){}
  ~CandidateGeneratorTheoryClass(){}
  void resetInstantiationRound(){};
  void reset( TNode n ){
    TheoryDatatypes::EqListsN::const_iterator i = d_th->d_equivalence_class.find(n);
    if(i == d_th->d_equivalence_class.end()){
      d_eqc = NULL;
    } else {
      d_eqc = (*i).second;
      d_eqc_i = d_eqc->begin();
    }
  }; //* the argument is not used
  TNode getNextCandidate(){
    if( d_eqc == NULL || d_eqc_i == d_eqc->end() ) return Node::null();
    return *(d_eqc_i++);
  };
};


}
}
}
}

#endif /* __CVC4__THEORY_DATATYPES_CANDIDATE_GENERATOR_H */
