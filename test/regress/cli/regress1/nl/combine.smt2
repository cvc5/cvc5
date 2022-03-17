; COMMAND-LINE: --nl-ext=full
; EXPECT: unsat
(set-logic QF_NRA)
(set-info :status unsat)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(assert (> c 1))
(assert (> (* a b) 1))

(assert (< (* a b c) 1))

(check-sat)
