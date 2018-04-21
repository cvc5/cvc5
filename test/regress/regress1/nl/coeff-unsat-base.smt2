; COMMAND-LINE: --nl-ext
; EXPECT: unsat
(set-logic QF_NRA)
(set-info :status unsat)

(declare-fun a () Real)
(declare-fun b () Real)

(assert (> a 0))
(assert (> b 0))

(assert (>= a (* 3 b)))

(assert (< (* a a) (* 3 a b)))

(check-sat)
