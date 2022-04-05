; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
(set-logic QF_LIA)
(declare-fun x0 () Bool)
(declare-fun x1 () Bool)
(declare-fun x2 () Bool)
(declare-fun x3 () Bool)
(declare-fun x4 () Bool)
(assert (not (and (or (and (and (and (or (not (and (not x4) (and x2 x4))) (not (or (or x2 x2) (or x0 x2)))) (not (and (or (or x2 x3) (or x0 x2)) (and (not x1) (not x1))))) (not (or (and (and (or x0 x4) (or x1 x1)) (and (and x3 x0) (not x1))) (or (not (and x3 x3)) (not (and x3 x1)))))) (or (not (not (not (not (and x3 x2))))) (not (or (or (not (or x0 x3)) (and (or x2 x2) (and x1 x0))) (not (and (and x2 x2) (or x0 x0))))))) (and (not (or (not (not (or (or x2 x3) (or x0 x4)))) (or (or (not (not x4)) (not (and x3 x3))) (and (not (not x0)) (and (not x2) (not x3)))))) (and (and (not (not (or (and x0 x1) (or x3 x4)))) (or (and (or (and x1 x2) (or x4 x1)) (or (or x4 x3) (not x4))) (not (and (not x1) (and x2 x1))))) (not (or (not (and (or x4 x0) (and x3 x2))) (not (and (and x0 x4) (not x0)))))))) (or (not (or (or (and (or (or (and x1 x1) (or x2 x1)) (and (not x3) (or x3 x1))) (and (and (and x3 x2) (and x0 x4)) (or (or x0 x4) (or x2 x4)))) (and (not (and (and x1 x2) (not x3))) (or (and (not x2) (or x3 x0)) (or (not x0) (not x2))))) (and (and (and (not (and x3 x3)) (not (not x0))) (or (or (and x0 x1) (not x2)) (not (or x3 x0)))) (or (and (or (and x0 x2) (and x0 x3)) (and (not x3) (or x0 x4))) (and (not (and x2 x1)) (not (not x1))))))) (and (not (not (and (not (or (not x4) (and x0 x0))) (or (not (not x0)) (or (and x1 x3) (and x2 x0)))))) (or (and (and (not (or (and x2 x1) (and x4 x1))) (and (not (and x0 x3)) (and (or x3 x2) (and x1 x4)))) (and (and (or (or x0 x1) (not x0)) (and (and x2 x3) (not x2))) (not (not (or x2 x3))))) (and (and (and (and (or x2 x1) (or x1 x4)) (and (and x2 x4) (or x1 x4))) (or (and (and x2 x0) (not x0)) (and (and x3 x1) (not x0)))) (or (not (or (not x4) (or x1 x2))) (and (or (not x2) (not x3)) (and (or x1 x2) (and x1 x1)))))))))))
(check-sat)
(push 1)
(check-sat)
(pop 1)
(check-sat)
(push 1)
(check-sat)
(push 1)
(assert (or (not (and (not (or (and (or x1 x0) (not x1)) (not (and x1 x3)))) (or (or (not (not x2)) (and (and x3 x3) (not x1))) (or (or (or x4 x3) (not x3)) (not (not x4)))))) (or (and (not (not (or (and x3 x3) (or x3 x0)))) (not (or (or (or x2 x4) (and x2 x1)) (or (not x2) (not x0))))) (and (not (or (and (not x1) (not x1)) (not (and x3 x0)))) (or (and (not (not x4)) (not (not x2))) (or (not (not x0)) (and (not x4) (or x2 x0))))))))
(check-sat)
(push 1)
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(assert (and x4 x0))
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (not x3))
(assert (not (or x0 x2)))
(check-sat)
(pop 1)
(assert (and (and (not x4) (not x2)) (not (or x1 x2))))
(check-sat)
