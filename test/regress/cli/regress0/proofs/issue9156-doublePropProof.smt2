; COMMAND-LINE: --strings-exp --check-proofs --check-unsat-cores
; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun a () String)
(assert (= (str.len a) 0))
(assert (str.contains (str.substr a 0 (- 1 0)) "G"))
(check-sat)