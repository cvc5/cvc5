; COMMAND-LINE: --produce-models
; EXPECT: unsat
(set-logic QF_AX)
(declare-const a (Array Bool Bool))
(declare-const b (Array Bool Bool))
(declare-const c Bool)
(declare-const d Bool)
(declare-const e Bool)
(assert (= a (store b c d)))
(assert (distinct e d (ite e c d)))
(assert (= e c (select b d)))
(check-sat)
