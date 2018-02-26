; COMMAND-LINE: --nl-ext
; EXPECT: unsat
(set-logic QF_NRA)
(set-info :status unsat)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(declare-fun d () Real)

(assert (>= a 1))
(assert (>= b 1))
(assert (>= c 1))
(assert (>= d 1))
(assert (or (= a 1) (= b 1) (= c 1) (= d 1)))

(assert (< (* a b c d) 1))

(check-sat)
