/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#ifndef CVC5__PARSER__ANTLR_TRACING_H
#define CVC5__PARSER__ANTLR_TRACING_H

// only enable the hack with -DCVC5_TRACE_ANTLR
#ifdef CVC5_TRACE_ANTLR

#include <iostream>
#include <string>

#include "base/output.h"

/* The ANTLR lexer generator, as of v3.2, puts Java trace commands
 * into our beautiful generated C lexer!  How awful!  This is clearly
 * a bug (the parser generator traces with printf()), but we have to
 * do something about it.  Basically, the things look like this:
 *
 *   System.out.println("something"+somethingElse+"another thing");
 *
 * What to do to make this C++?!  Alas, you cannot
 * "#define System.out.println", because it has dots in it.
 * So we do the following.  Sigh.
 *
 * This is all C++, and the generated lexer/parser is C++, but that's
 * ok here, we use the C++ compiler anyway!  Plus, this is only code
 * for **debugging** lexers and parsers.
 */

/** A "System" object, just like in Java! */
static struct __Cvc5System
{
  /**
   * Helper class just to handle arbitrary string concatenation
   * with Java syntax.  In C++ you cannot do "char*" + "char*",
   * so instead we fool the type system into calling
   * JavaPrinter::operator+() for each item successively.
   */
  struct JavaPrinter {
    template <class T>
    JavaPrinter operator+(const T& t) const {
      CVC5Message() << t;
      return JavaPrinter();
    }
  };/* struct JavaPrinter */

  /** A "System.out" object, just like in Java! */
  struct {
    /**
     * By the time println() is called, we've completely
     * evaluated (and thus printed) its entire argument, thanks
     * to the call-by-value semantics of C.  All that's left to
     * do is print the newline.
     */
    void println(JavaPrinter) { CVC5Message() << std::endl; }
  } out;
} System;

// Now define println(): this kicks off the successive operator+() calls
// Also define "failed" because ANTLR 3.3 uses "failed" improperly.
// These are highly dependent on the bugs in a particular ANTLR release.
// These seem to work with ANTLR 3.3 as of 4/23/2011.  A different trick
// works with ANTLR 3.2.  EXPECT LOTS OF COMPILER WARNINGS.
#define println(x)                   \
  println(({                         \
    int failed = 0;                  \
    __Cvc5System::JavaPrinter() + x; \
  }))
#undef ANTLR3_FPRINTF
#define ANTLR3_FPRINTF(args...) {int failed=0;fprintf(args);}
#undef ANTLR3_PRINTF
#define ANTLR3_PRINTF(args...) {int failed=0;printf(args);}

#endif /* CVC5_TRACE_ANTLR */

#endif /* CVC5__PARSER__ANTLR_TRACING_H */
