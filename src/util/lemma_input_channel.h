#include "cvc4_public.h"

#ifndef __CVC4__LEMMA_INPUT_CHANNEL_H
#define __CVC4__LEMMA_INPUT_CHANNEL_H

#include "expr/expr.h"

namespace CVC4 {

class CVC4_PUBLIC LemmaInputChannel {
public:
  virtual bool hasNewLemma() = 0;
  virtual Expr getNewLemma() = 0;

};/* class LemmaOutputChannel */

}/* CVC4 namespace */

#endif /* __CVC4__LEMMA_INPUT_CHANNEL_H */
