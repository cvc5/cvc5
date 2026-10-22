/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The native library of the cvc5 Java API.
 *
 * The Java API calls the cvc5 C API through the Foreign Function & Memory API
 * and contains no native code of its own. This library provides the C API
 * under the name that the Java API loads (see Utils.loadLibraries()): in a
 * static build, it contains cvc5 and its parser; in a shared build, it depends
 * on them.
 */

#include <cvc5/c/cvc5.h>
#include <cvc5/c/cvc5_parser.h>

extern "C" {
/**
 * Referenced so that the linker keeps the dependencies on cvc5 and its parser,
 * even when it only links libraries that are needed.
 */
void* cvc5_java_anchors[] = {
    reinterpret_cast<void*>(&cvc5_term_manager_new),
    reinterpret_cast<void*>(&cvc5_parser_new)};
}
