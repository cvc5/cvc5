; REQUIRES: glpk
; COMMAND-LINE: --use-approx
; EXPECT: sat
(set-logic QF_UFLIA)
(set-info :source "Reduced from regression 'issue2429.smt2' using ddSMT to exercise GLPK")
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status sat)
(declare-const x5 Int)
(declare-const x Int)
(assert (> (+ x (* 4 x5)) 1))
(check-sat)
