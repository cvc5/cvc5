; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
(set-logic QF_LIA)
(declare-fun x0 () Bool)
(declare-fun x1 () Bool)
(declare-fun x2 () Bool)
(assert (and (not (and (and (not (or (or (or x1 x2) (and x1 x2)) (and (and x2 x0) (not x2)))) (not (or (and (or x0 x2) (and x2 x1)) (not (or x1 x0))))) (not (and (not (not (and x1 x0))) (not (and (not x1) (or x1 x1))))))) (or (or (or (not (not (not (and x0 x0)))) (not (and (not (and x1 x2)) (not (not x2))))) (or (not (not (and (and x0 x2) (not x0)))) (and (and (not (not x2)) (not (and x0 x1))) (or (and (not x0) (and x1 x0)) (not (not x1)))))) (or (not (or (or (or (not x0) (and x0 x0)) (not (or x1 x1))) (or (not (or x0 x0)) (or (not x1) (or x1 x2))))) (and (or (not (not (and x0 x2))) (or (and (or x1 x1) (or x0 x0)) (and (or x1 x0) (not x1)))) (or (not (or (or x1 x2) (not x1))) (and (and (or x0 x1) (or x1 x2)) (or (not x1) (and x1 x0)))))))))
(check-sat)
(push 1)
(assert (and (or (not (not x2)) (and (not x2) (and x0 x0))) (and (not (and x1 x0)) (or (not x2) (or x0 x1)))))
(assert (or (or x2 x2) (not x2)))
(check-sat)
(pop 1)
(assert (or (and (not (not (and (and (or (not (and (not x2) (or x0 x2))) (not (or (or x0 x2) (not x1)))) (or (not (and (not x2) (and x2 x0))) (and (or (and x0 x0) (and x2 x2)) (not (not x1))))) (not (and (and (or (and x1 x1) (and x2 x0)) (and (and x1 x0) (or x1 x0))) (and (not (and x0 x0)) (or (and x0 x2) (and x0 x2)))))))) (or (not (not (not (and (not (and (and x0 x0) (or x1 x2))) (not (or (or x2 x1) (not x2))))))) (and (or (not (and (and (and (and x1 x0) (or x1 x1)) (not (or x2 x0))) (or (or (and x1 x1) (or x2 x1)) (not (or x2 x0))))) (or (and (or (and (not x0) (or x1 x2)) (not (not x0))) (not (and (and x2 x1) (and x1 x2)))) (not (or (or (and x0 x1) (or x1 x2)) (or (not x2) (not x2)))))) (not (and (not (or (or (and x2 x0) (not x0)) (not (not x2)))) (and (or (or (and x0 x1) (and x2 x2)) (or (or x0 x0) (or x2 x0))) (not (not (not x1))))))))) (not (not (not (and (or (not (and (or (and x1 x2) (or x1 x1)) (not (or x0 x1)))) (not (not (not (or x1 x2))))) (or (and (not (or (and x0 x2) (or x2 x1))) (not (not (and x1 x2)))) (and (not (or (not x2) (not x1))) (not (not (not x1)))))))))))
(assert (not x0))
(check-sat)
(push 1)
(assert (not (or (or x2 x0) (and x1 x1))))
(assert (or (or (not (and (or (not x0) (not x2)) (and (and x1 x1) (or x1 x0)))) (not (not (not (not x2))))) (and (not (or (and (not x1) (or x1 x1)) (not (not x1)))) (not (or (not (not x2)) (not (not x0)))))))
(assert (not (and x0 x0)))
(check-sat)
