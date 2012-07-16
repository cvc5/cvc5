#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"

namespace CVC4 {
namespace smt {

CVC4_THREADLOCAL(SmtEngine*) s_smtEngine_current = NULL;

}
}
