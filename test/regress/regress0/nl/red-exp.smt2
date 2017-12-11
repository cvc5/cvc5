; COMMAND-LINE: --nl-ext
; EXPECT: unsat
(set-logic QF_NRA)
(set-info :status unsat)

(declare-fun a () Real)
(declare-fun b () Real)

(assert (or (= a (* b b)) (and (= a 9) (= b 3))))
(assert (not (= (* a a) (* b b b b))))
(check-sat)
