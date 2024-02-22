#include "expr/node.h"
#include "expr/node_manager.h"
#include "proof/proof_checker.h"
#include "rewriter/rewrite_db.h"
#include "rewriter/rewrites.h"
#include "theory/builtin/generic_op.h"
#include "util/string.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace rewriter {

// clang-format off
void ${rewrite_name}$(RewriteDb& db)
// clang-format on
{
  NodeManager* nm = NodeManager::currentNM();

  // Variables
  // clang-format off
${decls}$

  // Definitions
${defns}$

  // Rules
${rules}$
  // clang-format on
}

}  // namespace rewriter
}  // namespace cvc5::internal
