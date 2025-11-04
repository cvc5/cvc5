###############################################################################
# Top contributors (to current version):
#   Daniel Larraz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# "Ouroborous" test: does cvc5 read its own output?
#
# The "Ouroborous" test, named after the serpent that swallows its
# own tail, ensures that cvc5 can parse some input, output it again
#  (in any of its languages) and then parse it again.  The result of
# the first parse must be equal to the result of the second parse;
# both strings and expressions are compared for equality.
#
# To add a new test, simply add a call to run_test_string() under
# run_test(), below.  If you don't specify an input language,
# LANG_SMTLIB_V2 is used.  If your example depends on symbolic constants,
# you'll need to declare them in the "declarations" global, just
# below, in SMT-LIBv2 form (but they're good for all languages).
##

import cvc5

def parse(instr: str, input_language: str, output_language: str) -> str:
    assert input_language == "smt2"
    assert output_language == "smt2"

    declarations = """(set-logic ALL)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun x () U)
(declare-fun y () U)
(assert (= (f x) x))
(declare-fun a () (Array U (Array U U)))
"""

    tm = cvc5.TermManager()
    solver = cvc5.Solver(tm)

    solver.setOption("input-language", input_language)
    solver.setOption("output-language", output_language)

    sm = cvc5.SymbolManager(tm)
    parser = cvc5.InputParser(solver, sm)

    # Parse declarations to bind symbols
    parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, declarations, "internal-buffer")
    while True:
        cmd = parser.nextCommand()
        if cmd.isNull():
            break
        # Invoke the command, which may bind symbols
        cmd.invoke(solver, sm)

    assert parser.done() # parser should be done

    parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, instr, "internal-buffer")
    term = parser.nextTerm()
    s = str(term)
    assert parser.nextTerm().isNull()  # next expr should be null
    return s

def translate(instr: str, input_language: str, output_language: str) -> str:
    print("="*50)
    print(f"translating from {input_language} to {output_language} this string:")
    print(instr)
    outstr = parse(instr, input_language, output_language)
    print("got this:")
    print(outstr)
    print(f"reparsing as {output_language}")
    poutstr = parse(outstr, output_language, output_language)
    assert outstr == poutstr
    print(f"got same expressions {outstr} and {poutstr}")
    print("="*50)
    return outstr

def run_test_string(instr: str, instr_language: str):
    print(f"\nstarting with: {instr}\n   in language {instr_language}")
    smt2str = translate(instr, instr_language, "smt2")
    print(f"in SMT2      : {smt2str}")
    outstr = translate(smt2str, "smt2", "smt2")
    print(f"to SMT2 : {outstr}\n")
    assert outstr == smt2str

def run_test():
    run_test_string("(= (f (f y)) x)", "smt2")
    run_test_string("(= ((_ extract 2 1) (bvnot (bvadd #b000 #b011))) #b10)", "smt2")
    run_test_string("((_ extract 2 0) (bvnot (bvadd (bvmul #b001 #b011) #b011)))", "smt2")

run_test()
