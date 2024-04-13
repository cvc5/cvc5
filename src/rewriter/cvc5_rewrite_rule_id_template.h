/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Jörg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Generated rewrite proof rules.
 */

#if (!defined(CVC5_API_USE_C_ENUMS)                      \
     && !defined(CVC5__API__CVC5_CPP_REWRITE_RULE_ID_H)) \
    || (defined(CVC5_API_USE_C_ENUMS)                    \
        && !defined(CVC5__API__CVC5_C_REWRITE_RULE_ID_H))

#ifdef CVC5_API_USE_C_ENUMS
#include <stddef.h>
#include <stdint.h>
#undef ENUM
#define ENUM(name) Cvc5##name
#else
#include <cvc5/cvc5_export.h>

#include <cstdint>
#include <ostream>
namespace cvc5 {
#undef ENUM
#define ENUM(name) class name
#undef EVALUE
#define EVALUE(name) name
#endif

#ifdef CVC5_API_USE_C_ENUMS
#undef EVALUE
#define EVALUE(name) CVC5_REWRITE_RULE_ID_##name
#endif

/**
 * Identifiers for rewrite proof rules.
 */
enum ENUM(RewriteRuleId) : uint32_t
{
  EVALUE(NONE),
  // Generated rule ids
  // clang-format off
  ${rule_ids}$,
// clang-format on
#ifdef CVC5_API_USE_C_ENUMS
  // must be last entry
  EVALUE(LAST)
#endif
};

#ifdef CVC5_API_USE_C_ENUMS
#ifndef DOXYGEN_SKIP
typedef enum ENUM(RewriteRuleId) ENUM(RewriteRuleId);
#endif
#endif

#ifdef CVC5_API_USE_C_ENUMS

/**
 * Get a string representation of a Cvc5RewriteRuleId.
 * @param id The rewrite proof rule.
 * @return The string representation.
 */
const char* cvc5_rewrite_rule_id_to_string(Cvc5RewriteRuleId id);

/**
 * Hash function for Cvc5RewriteRuleId.
 * @param id The rewrite proof rule.
 * @return The hash value.
 */
size_t cvc5_rewrite_rule_id_hash(Cvc5RewriteRuleId id);

#else

/**
 * Converts a rewrite proof rule to a string. Note: This function is also
 * used in `safe_print()`. Changing this function name or signature will result
 * in `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param id The rewrite proof rule
 * @return The name of the proof rule
 */
const char* toString(RewriteRuleId id);

/**
 * Writes a rewrite proof rule name to a stream.
 *
 * @param out The stream to write to
 * @param id The rewrite proof rule to write to the stream
 * @return The stream
 */
CVC5_EXPORT std::ostream& operator<<(std::ostream& out, RewriteRuleId id);

}  // namespace cvc5

namespace std {
/**
 * Hash function for RewriteRuleIds.
 */
template <>
struct CVC5_EXPORT hash<cvc5::RewriteRuleId>
{
  /**
   * Hashes a RewriteRuleId to a size_t.
   * @param id The rewrite proof rule.
   * @return The hash value.
   */
  size_t operator()(cvc5::RewriteRuleId id) const;
};
/**
 * Converts a rewrite proof rule to a string.
 *
 * @param id The rewrite proof rule
 * @return The name of the rewrite proof rule
 */
std::string to_string(cvc5::RewriteRuleId id);
}  // namespace std

#endif
#endif

#ifdef CVC5_API_USE_C_ENUMS
#ifndef CVC5__API__CVC5_C_REWRITE_RULE_ID_H
#define CVC5__API__CVC5_C_REWRITE_RULE_ID_H
#endif
#else
#ifndef CVC5__API__CVC5_CPP_REWRITE_RULE_ID_H
#define CVC5__API__CVC5_CPP_REWRITE_RULE_ID_H
#endif
#endif
