; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: sat
(set-logic QF_LIA)
(declare-fun x0 () Bool)
(declare-fun x1 () Bool)
(declare-fun x2 () Bool)
(declare-fun x3 () Bool)
(assert (or (and (not (or (and (and (not (not (and x1 x2))) (and (not (not x1)) (not (and x3 x0)))) (not (or (and (and x0 x2) (or x3 x3)) (not (not x1))))) (not (or (and (not (not x1)) (not (not x0))) (not (or (or x0 x3) (not x0))))))) (or (and (and (not (or (or (and x2 x2) (or x1 x2)) (not (and x3 x3)))) (not (or (not (not x2)) (and (and x2 x1) (and x1 x1))))) (or (or (and (not (or x2 x3)) (or (not x0) (and x1 x1))) (or (or (or x3 x2) (and x2 x3)) (or (and x1 x0) (not x3)))) (or (and (not (or x3 x3)) (or (and x2 x2) (or x3 x0))) (and (not (or x0 x2)) (and (not x1) (or x2 x3)))))) (not (not (not (or (not (not x3)) (or (and x0 x3) (or x0 x3)))))))) (not (or (or (or (not (or (or (and x3 x0) (not x3)) (or (and x2 x0) (and x1 x2)))) (and (or (not (and x0 x2)) (not (or x1 x1))) (or (or (or x3 x1) (or x1 x2)) (or (not x1) (and x1 x1))))) (not (not (not (and (and x0 x3) (or x1 x1)))))) (and (and (and (and (and (or x3 x0) (or x1 x3)) (and (not x1) (not x2))) (not (not (not x0)))) (not (and (or (and x3 x3) (or x2 x3)) (not (or x1 x1))))) (and (or (not (and (and x0 x2) (not x0))) (or (not (or x3 x0)) (not (or x1 x0)))) (or (and (and (and x2 x0) (not x1)) (not (not x0))) (and (or (not x3) (or x1 x1)) (not (and x0 x3))))))))))
(check-sat)
(push 1)
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (or (not (and x0 x2)) (and (not x2) (and x0 x2))))
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (or (and (or (not (or (or (and (not (or x3 x3)) (or (not x1) (or x0 x2))) (and (or (and x3 x1) (or x3 x3)) (not (or x1 x3)))) (or (or (not (and x3 x2)) (not (or x1 x1))) (or (and (or x0 x1) (and x0 x1)) (and (or x0 x2) (and x1 x1)))))) (not (and (not (not (not (and x0 x1)))) (or (and (or (or x1 x3) (not x3)) (and (and x3 x1) (and x1 x1))) (not (not (not x1))))))) (not (and (or (and (or (not (and x0 x3)) (and (or x0 x0) (or x0 x0))) (and (and (or x1 x0) (and x1 x2)) (and (not x3) (or x0 x1)))) (and (not (or (not x0) (not x2))) (or (or (and x0 x0) (not x0)) (and (not x1) (and x2 x3))))) (and (and (not (or (and x3 x1) (or x0 x1))) (not (or (or x2 x2) (not x2)))) (not (or (and (and x2 x3) (or x2 x0)) (or (and x0 x0) (not x2)))))))) (not (or (or (or (and (and (or (and x2 x0) (not x3)) (or (or x0 x1) (not x2))) (not (and (not x3) (not x2)))) (not (and (and (and x0 x0) (not x3)) (and (not x3) (and x0 x2))))) (not (not (and (and (and x2 x1) (not x3)) (or (or x3 x2) (not x2)))))) (not (or (not (or (not (and x0 x0)) (or (not x3) (or x3 x3)))) (or (and (or (and x0 x3) (not x2)) (not (not x2))) (or (not (or x0 x3)) (or (and x1 x2) (and x1 x0))))))))))
(check-sat)
(pop 1)
(check-sat)
