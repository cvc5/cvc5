; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
(set-logic QF_LIA)
(declare-fun x0 () Bool)
(declare-fun x1 () Bool)
(declare-fun x2 () Bool)
(declare-fun x3 () Bool)
(check-sat)
(push 1)
(assert (not (or (not x1) (or x1 x0))))
(assert (and (and x2 x1) (not x0)))
(assert (not (not (or (not (and (not x2) (or x2 x3))) (not (and (not x2) (and x3 x3)))))))
(assert (and (not (and (not x3) (not x0))) (and (not (or x3 x3)) (or (not x2) (or x0 x1)))))
(assert (and (not (and (not (not (and (and (or (and x0 x0) (and x1 x0)) (or (or x2 x1) (and x1 x1))) (and (or (or x0 x3) (and x1 x0)) (not (and x0 x3)))))) (or (and (not (not (not (or x2 x3)))) (not (and (and (or x2 x1) (not x3)) (and (or x1 x1) (or x3 x1))))) (and (and (and (not (and x2 x3)) (or (or x3 x3) (or x2 x2))) (not (not (or x2 x2)))) (and (and (or (and x0 x0) (and x1 x1)) (not (or x3 x0))) (and (or (or x3 x3) (and x3 x2)) (or (not x0) (not x0)))))))) (not (or (or (and (and (not (or (not x1) (or x3 x3))) (and (and (not x0) (and x1 x3)) (and (and x3 x1) (not x2)))) (and (or (and (not x1) (not x1)) (and (not x1) (or x0 x2))) (not (and (or x1 x1) (and x2 x2))))) (or (or (and (or (or x3 x1) (and x1 x3)) (or (not x3) (not x3))) (or (or (not x0) (not x1)) (and (and x3 x2) (or x0 x3)))) (not (or (not (or x1 x0)) (or (and x3 x3) (or x0 x2)))))) (and (not (or (not (not (and x2 x3))) (not (not (and x1 x3))))) (or (not (and (or (and x0 x3) (or x0 x0)) (not (not x2)))) (not (and (not (and x3 x3)) (not (and x1 x2))))))))))
(assert (not (or (not (or (not (and (and (and x1 x2) (not x1)) (or (or x1 x1) (or x3 x3)))) (not (or (not (not x3)) (and (and x3 x0) (or x3 x3)))))) (not (and (not (and (or (and x3 x2) (and x1 x0)) (not (not x2)))) (or (not (not (or x3 x1))) (or (not (not x2)) (and (or x1 x2) (and x1 x1)))))))))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (or (or (and (or (not x1) (not x2)) (and (or x1 x1) (and x0 x2))) (not (not (not x0)))) (or (or (not (or x1 x2)) (and (not x3) (or x0 x2))) (not (or (not x2) (or x3 x1))))))
(check-sat)
(push 1)
(assert (not (not (and x2 x0))))
(assert (not (and (and (and (not (and (or (or x0 x3) (not x0)) (not (and x3 x0)))) (and (or (and (and x3 x2) (not x2)) (and (not x1) (or x1 x3))) (and (or (not x3) (or x3 x3)) (and (or x0 x2) (not x0))))) (or (and (not (not (not x2))) (or (and (and x1 x0) (or x3 x1)) (and (or x3 x0) (not x0)))) (and (not (not (and x2 x2))) (and (not (and x0 x2)) (not (or x2 x1)))))) (or (or (not (not (and (and x3 x3) (or x1 x0)))) (or (not (not (or x0 x0))) (or (not (not x1)) (or (not x3) (not x2))))) (not (and (and (and (or x0 x1) (and x0 x0)) (not (and x3 x1))) (not (and (and x0 x0) (not x1)))))))))
(check-sat)
(pop 1)
(assert (not (not (or (and (or x0 x2) (not x1)) (and (or x2 x0) (not x2))))))
(assert (and (or (and (not x0) (not x2)) (not (not x3))) (or (not (or x0 x0)) (and (not x0) (and x2 x3)))))
(check-sat)
