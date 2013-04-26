#include "theory/arith/callbacks.h"
#include "theory/arith/theory_arith_private.h"

namespace CVC4 {
namespace theory {
namespace arith {

void SetupLiteralCallBack::operator()(TNode lit){
  TNode atom = (lit.getKind() == kind::NOT) ? lit[0] : lit;
  if(!d_arith.isSetup(atom)){
    d_arith.setupAtom(atom);
  }
}

Rational DeltaComputeCallback::operator()() const{
  return d_ta.deltaValueForTotalOrder();
}

ArithVar TempVarMalloc::request(){
  Node skolem = mkRealSkolem("tmpVar");
  return d_ta.requestArithVar(skolem, false);
}
void TempVarMalloc::release(ArithVar v){
  d_ta.releaseArithVar(v);
}

void BasicVarModelUpdateCallBack::operator()(ArithVar x){
  d_ta.signal(x);
}

void RaiseConflict::operator()(Node n){
  d_ta.raiseConflict(n);
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
