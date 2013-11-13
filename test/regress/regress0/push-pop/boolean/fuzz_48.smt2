; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
(set-logic QF_LIA)
(declare-fun x0 () Bool)
(declare-fun x1 () Bool)
(declare-fun x2 () Bool)
(declare-fun x3 () Bool)
(declare-fun x4 () Bool)
(declare-fun x5 () Bool)
(assert (and (or (not (not (and x0 x4))) (and (not (not x2)) (not (not x4)))) (not (or (not (or x2 x5)) (and (not x4) (not x1))))))
(assert (and (and (not (and (and (not (and (and (and x5 x0) (not x4)) (or (and x0 x0) (or x0 x0)))) (or (or (not (or x5 x2)) (or (not x3) (or x4 x2))) (not (and (and x1 x0) (not x0))))) (and (not (or (and (or x1 x3) (and x1 x0)) (and (and x2 x0) (and x2 x3)))) (not (not (or (not x5) (not x5))))))) (or (or (or (and (or (and (not x2) (or x1 x0)) (not (not x1))) (and (and (and x4 x3) (or x4 x3)) (and (not x5) (or x0 x2)))) (and (not (not (not x2))) (or (or (or x2 x1) (or x3 x2)) (and (or x2 x2) (and x4 x2))))) (not (or (or (and (or x1 x5) (or x3 x5)) (not (not x5))) (not (and (not x3) (not x3)))))) (not (or (and (or (or (or x4 x4) (or x0 x2)) (not (or x0 x4))) (or (or (or x2 x1) (or x1 x4)) (or (or x4 x4) (or x1 x5)))) (and (not (or (or x3 x4) (or x2 x0))) (not (not (or x2 x3)))))))) (and (or (or (not (not (not (and (not x2) (or x1 x2))))) (and (not (or (and (and x5 x3) (not x3)) (or (and x4 x0) (not x0)))) (not (not (and (and x0 x5) (and x3 x1)))))) (not (and (not (and (not (or x1 x3)) (not (or x1 x5)))) (not (not (not (or x1 x1))))))) (not (and (or (or (not (not (not x0))) (and (not (not x1)) (or (not x0) (or x4 x3)))) (or (and (or (and x4 x0) (and x1 x2)) (or (not x1) (not x5))) (or (or (or x3 x0) (or x3 x4)) (or (or x3 x4) (and x1 x2))))) (not (and (not (or (not x3) (not x3))) (and (and (or x5 x1) (not x2)) (or (or x5 x4) (or x0 x5))))))))))
(check-sat)
(push 1)
(assert (and x0 x1))
(check-sat)
(push 1)
(assert (and (or (and (and (or (or (not (or x4 x3)) (or (or x1 x0) (or x5 x3))) (and (or (not x0) (not x5)) (or (and x5 x0) (and x5 x0)))) (not (and (and (and x0 x1) (not x2)) (not (or x3 x3))))) (and (not (and (not (and x3 x1)) (not (not x1)))) (not (and (or (or x1 x0) (or x4 x4)) (or (not x5) (and x3 x4)))))) (or (not (or (not (or (and x3 x2) (or x0 x2))) (or (not (and x0 x0)) (and (not x4) (not x3))))) (not (or (and (and (or x5 x3) (and x2 x5)) (not (or x4 x4))) (or (not (not x1)) (or (or x3 x4) (not x5))))))) (not (and (and (not (not (or (not x0) (or x1 x4)))) (and (or (or (not x1) (not x5)) (not (or x2 x3))) (and (and (and x5 x3) (not x2)) (not (not x5))))) (or (or (and (and (and x0 x4) (not x5)) (not (or x0 x0))) (or (not (or x0 x4)) (and (not x1) (or x2 x0)))) (and (not (or (or x4 x2) (or x3 x3))) (and (and (and x5 x3) (and x4 x3)) (and (not x4) (not x1)))))))))
(check-sat)
(pop 1)
(assert (not (not (not (and (or (or (and (or x4 x3) (and x1 x4)) (and (or x3 x0) (not x0))) (and (and (or x1 x4) (and x3 x5)) (or (or x1 x5) (and x0 x1)))) (or (and (not (not x5)) (or (or x0 x2) (and x5 x0))) (and (or (not x2) (not x4)) (or (and x2 x5) (not x0)))))))))
(check-sat)
