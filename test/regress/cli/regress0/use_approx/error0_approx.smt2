; REQUIRES: glpk
; COMMAND-LINE: --use-approx
; EXPECT: sat
(set-logic QF_UFLIA)
(set-info :source "Reduced from regression 'error0.smt2' using ddSMT to exercise GLPK")
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun a () Int)
(declare-fun x (Int) Int)
(assert (> 0 (+ a (* 2 (x 0)))))
(assert (< 0 (+ a 1)))
(check-sat)
