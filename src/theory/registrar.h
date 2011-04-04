#include "cvc4_private.h"

#ifndef __CVC4__THEORY_REGISTRAR_H
#define __CVC4__THEORY_REGISTRAR_H
#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

class Registrar {
private:
  TheoryEngine* d_theoryEngine;

public:
  Registrar() : d_theoryEngine(NULL){ }

  Registrar(TheoryEngine* te) : d_theoryEngine(te){ }

  void preRegister(Node n){
    if(d_theoryEngine != NULL){
      d_theoryEngine->preRegister(n);
    }
  }

};/* class Registrar */


}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_REGISTRAR_H */
