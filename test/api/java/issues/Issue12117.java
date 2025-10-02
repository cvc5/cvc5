/******************************************************************************
 * Top contributors (to current version):
 *   Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for issue #12117
 */

import io.github.cvc5.*;

public class Issue12117 {
    public static void main(String[] args) {
        TermManager tm = new TermManager();
        try {
            // Attempt to create a string term with a high Unicode surrogate
            Term t = tm.mkString("\uD880\uDC4C");
            System.out.println("Term created: " + t);
        } catch (CVC5ApiException e) {
            System.out.println("Exception occurred: " + e.getMessage());
        }
    }
}
