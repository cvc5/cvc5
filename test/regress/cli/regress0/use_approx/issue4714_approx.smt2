; REQUIRES: glpk
; COMMAND-LINE: --use-approx
; EXPECT: sat
(set-logic UFNIRA)
(set-info :source "Reduced from regression 'issue2429.smt2' using ddSMT to exercise GLPK")
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun c (Int) Int)
(assert (exists ((l Int) (k Int)) (and (< 0 l) (< l (- (c k) 1)) (distinct 0 (mod (mod 0 (c 0)) (c k))))))
(check-sat)
