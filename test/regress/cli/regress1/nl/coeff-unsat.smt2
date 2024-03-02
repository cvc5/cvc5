; COMMAND-LINE: --nl-ext=full
; EXPECT: unsat
;; Logic not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic QF_NRA)
(set-info :status unsat)

(declare-fun a () Real)
(declare-fun b () Real)

(assert (> a 0))
(assert (> b 0))

(assert (>= a (* 3 b)))

(assert (< (* a a) (* 8 b b)))

(check-sat)
