; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: (a (< x 3))
; EXPECT: unsat
; EXPECT: ((and (= x 5) (= y 7)) (> x 6))
; EXPECT: unsat
; EXPECT: (b)
; EXPECT: sat
; EXPECT: unsat
; EXPECT: ()
(set-option :produce-unsat-assumptions true)
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (=> a (> x 5)))
(assert (> y 0))
(check-sat-assuming (a (< x 3)))
(get-unsat-assumptions)
(check-sat-assuming ((and (= x 5) (= y 7)) (> x 6) b))
(get-unsat-assumptions)
(push 1)
(assert (=> b (< y 0)))
(check-sat-assuming (b))
(get-unsat-assumptions)
(pop 1)
(check-sat-assuming (b))
(assert (< y 0))
(check-sat-assuming (a))
(get-unsat-assumptions)
