; COMMAND-LINE: --incremental
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
(assert (not (and (not (and (or (not (or (not x0) (or x2 x2))) (or (or (or x2 x1) (or x1 x3)) (not (or x3 x2)))) (or (not (not (and x1 x2))) (and (not (not x2)) (and (or x0 x2) (or x0 x1)))))) (not (not (or (or (and (or x0 x1) (not x3)) (and (or x3 x3) (and x3 x1))) (not (or (or x0 x2) (or x2 x3)))))))))
(assert (and (not (and (and (not (not (not x2))) (and (or (or x3 x0) (not x1)) (and (or x0 x0) (and x1 x1)))) (and (and (and (and x0 x3) (and x2 x1)) (or (not x3) (not x0))) (not (and (and x2 x0) (and x2 x1)))))) (and (or (or (and (not (or x0 x1)) (not (and x2 x3))) (and (not (not x0)) (or (or x3 x1) (or x1 x2)))) (or (or (or (not x0) (and x0 x1)) (and (and x2 x2) (or x3 x3))) (or (not (or x1 x1)) (and (and x0 x3) (and x3 x2))))) (or (not (not (not (and x3 x1)))) (or (and (not (and x0 x2)) (not (or x0 x1))) (and (not (and x3 x3)) (not (not x1))))))))
(assert (not (and x0 x3)))
(check-sat)
(push 1)
(assert (or (or (or x0 x1) (and x0 x1)) (or (and x0 x2) (not x1))))
(assert (or (or (or (or (not (not (or (or (or x3 x2) (not x1)) (or (and x3 x2) (not x3))))) (not (and (not (and (or x1 x0) (or x0 x1))) (or (and (or x1 x3) (or x1 x1)) (and (and x0 x3) (and x2 x0)))))) (and (and (not (not (and (and x3 x3) (not x3)))) (not (or (or (and x0 x0) (not x2)) (not (and x1 x1))))) (not (or (and (or (or x1 x0) (or x2 x2)) (and (and x2 x2) (not x1))) (not (not (not x0))))))) (or (not (and (not (and (or (and x0 x0) (not x1)) (or (not x3) (or x0 x1)))) (not (and (and (or x3 x1) (or x1 x2)) (not (not x3)))))) (and (not (not (and (or (not x2) (not x1)) (and (not x3) (or x0 x3))))) (or (or (and (not (or x1 x3)) (or (not x0) (and x1 x3))) (and (not (or x2 x2)) (or (and x1 x3) (or x1 x1)))) (not (not (not (or x1 x3)))))))) (and (not (not (not (or (not (or (or x1 x2) (not x2))) (or (or (or x3 x3) (or x1 x0)) (and (and x3 x3) (not x1))))))) (and (not (not (or (or (and (or x0 x3) (or x0 x0)) (and (and x2 x3) (not x3))) (or (or (not x3) (and x3 x3)) (not (not x2)))))) (and (not (and (not (or (or x1 x0) (not x2))) (and (and (or x0 x0) (and x2 x2)) (not (and x2 x0))))) (and (and (or (and (or x2 x1) (not x1)) (not (not x1))) (not (not (and x0 x0)))) (not (not (not (and x0 x1))))))))))
(assert (or (not (or (not x1) (or x1 x1))) (and (not (or x0 x3)) (or (and x1 x3) (not x3)))))
(assert (not (and (not (or (and (or x2 x1) (and x3 x0)) (and (not x1) (or x0 x3)))) (or (not (not (and x2 x3))) (and (and (and x0 x2) (not x0)) (or (and x0 x1) (not x0)))))))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (and (not (and x3 x2)) (or (and x2 x1) (not x0))))
(assert (or (or (not (or (and (not x0) (not x0)) (not (and x0 x3)))) (not (or (and (and x3 x1) (or x0 x0)) (and (and x0 x3) (and x3 x3))))) (or (and (or (and (not x0) (or x1 x1)) (not (or x2 x0))) (not (or (and x0 x2) (and x0 x0)))) (not (and (or (or x2 x0) (and x2 x3)) (and (or x2 x0) (not x0)))))))
(assert (not (not (or (or x0 x3) (or x1 x2)))))
(assert (or (and (or (and x0 x0) (and x3 x0)) (not (and x0 x0))) (not (or (and x2 x2) (not x1)))))
(check-sat)
(pop 1)
(assert (and (or (not (and x2 x2)) (and (and x2 x3) (not x3))) (and (not (or x0 x1)) (not (and x1 x2)))))
(check-sat)
