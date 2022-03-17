; REQUIRES: glpk
; COMMAND-LINE: --use-approx
; EXPECT: sat
(set-logic QF_NIA)
(set-info :source "Reduced from regression 'issue4714.smt2' using ddSMT to exercise GLPK")
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status sat)
(declare-const x Bool)
(declare-const n Int)
(declare-const j Int)
(assert (< j n))
(assert (or x (= 0 (+ n j))))
(check-sat)
