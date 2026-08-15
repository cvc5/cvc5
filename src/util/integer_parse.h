/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Syntax of the string representation of an Integer.
 */

#include "cvc5_private.h"

#ifndef CVC5__INTEGER_PARSE_H
#define CVC5__INTEGER_PARSE_H

#include <string>

namespace cvc5::internal {

/**
 * Determine whether s is a valid string representation of an integer in the
 * given base.
 *
 * The accepted syntax is an optional '-' followed by a magnitude. For a base
 * in [2,36] the magnitude is a non-empty sequence of digits valid in that
 * base, upper or lower case. For base 0 the base of the magnitude is inferred:
 * "0x"/"0X" followed by at least one hexadecimal digit is hexadecimal,
 * "0b"/"0B" followed by at least one binary digit is binary, a leading '0'
 * followed by any number of octal digits is octal, and anything else is
 * decimal. Leading zeroes are permitted.
 *
 * Both underlying arithmetic libraries accept strings outside this syntax, but
 * they do not accept the same ones, so the Integer implementations reject
 * anything this function rejects in order to behave identically. In particular
 * GMP silently ignores whitespace anywhere in the string and reads a bare
 * "0x" as zero, while CLN reads "" and "-" as zero and accepts a leading '+'.
 *
 * Note this is a purely syntactic check and is deliberately more permissive
 * than the SMT-LIB <numeral> syntax enforced at the API level, which allows
 * neither leading zeroes nor a base prefix.
 *
 * @param s The string to check.
 * @param base The base, where 0 means the base is inferred from s.
 * @return True if s is a valid representation of an integer in the given base.
 */
bool isValidIntegerLiteral(const std::string& s, unsigned base);

}  // namespace cvc5::internal

#endif /* CVC5__INTEGER_PARSE_H */
