; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
(set-logic QF_LIA)
(declare-fun x0 () Bool)
(declare-fun x1 () Bool)
(declare-fun x2 () Bool)
(declare-fun x3 () Bool)
(declare-fun x4 () Bool)
(declare-fun x5 () Bool)
(declare-fun x6 () Bool)
(declare-fun x7 () Bool)
(check-sat)
(push 1)
(assert (not (not (or (and (not (and (or (not (or (not x4) (and x6 x0))) (or (and (and x4 x4) (not x1)) (not (not x0)))) (not (not (or (not x7) (or x1 x1)))))) (not (and (and (not (and (and x4 x3) (and x0 x4))) (and (not (and x5 x4)) (and (not x2) (or x5 x5)))) (not (not (not (not x3))))))) (not (not (and (or (not (not (and x7 x3))) (and (and (not x4) (or x3 x2)) (or (or x7 x0) (not x0)))) (not (not (or (and x7 x6) (or x1 x2)))))))))))
(assert (not (or (or (and (or (or (not (and x2 x1)) (and (or x4 x1) (or x4 x0))) (and (and (not x3) (not x6)) (not (or x5 x6)))) (not (not (and (or x6 x5) (not x4))))) (and (not (not (or (and x7 x6) (not x3)))) (or (and (not (not x4)) (and (not x0) (or x7 x2))) (and (and (or x3 x3) (not x6)) (or (or x0 x6) (or x1 x4)))))) (and (or (and (or (or (and x5 x1) (and x5 x5)) (or (or x5 x3) (or x0 x3))) (not (or (and x5 x1) (and x7 x6)))) (not (and (and (and x1 x7) (and x5 x4)) (and (not x1) (or x4 x6))))) (not (and (or (and (not x2) (and x6 x4)) (not (and x1 x6))) (not (not (or x7 x5)))))))))
(assert (or (not (or (and (and (and (and (not x2) (not x0)) (not (and x4 x5))) (and (or (not x7) (not x7)) (or (not x6) (or x4 x3)))) (or (or (not (not x1)) (or (not x5) (not x4))) (and (and (and x4 x4) (or x2 x1)) (and (not x7) (and x1 x2))))) (or (not (not (not (or x2 x7)))) (or (and (or (or x5 x2) (not x3)) (or (not x2) (and x6 x6))) (or (and (and x7 x3) (and x6 x2)) (not (not x0))))))) (and (and (or (and (or (or (or x5 x3) (or x3 x5)) (and (not x2) (or x0 x4))) (or (not (and x2 x7)) (or (not x2) (or x7 x6)))) (or (and (or (and x5 x0) (not x1)) (not (or x5 x6))) (not (not (or x6 x5))))) (or (and (and (and (and x3 x1) (or x4 x6)) (and (or x6 x4) (or x6 x5))) (or (and (not x1) (or x1 x6)) (or (and x6 x4) (and x4 x1)))) (not (and (not (and x7 x5)) (or (and x1 x3) (or x4 x1)))))) (or (and (or (or (and (not x6) (not x6)) (not (or x0 x6))) (or (not (not x5)) (or (and x7 x7) (or x6 x4)))) (or (or (and (or x1 x1) (not x5)) (and (not x6) (or x3 x4))) (or (not (not x1)) (or (or x1 x6) (or x6 x3))))) (and (not (or (not (and x6 x3)) (and (or x4 x6) (and x7 x3)))) (or (and (and (and x4 x6) (and x6 x2)) (or (and x4 x3) (and x0 x1))) (and (and (or x3 x7) (or x1 x2)) (and (not x7) (or x0 x6)))))))))
(check-sat)
(push 1)
(assert (or (not (or (not (or (or x2 x0) (and x5 x6))) (and (not (and x5 x6)) (or (or x2 x3) (not x3))))) (and (not (or (not (or x7 x6)) (or (not x6) (or x7 x7)))) (or (or (and (or x5 x6) (or x7 x4)) (not (not x2))) (or (or (or x2 x0) (and x1 x6)) (and (and x2 x2) (not x4)))))))
(check-sat)
(push 1)
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (not (or (or (and x5 x3) (or x4 x4)) (and (not x4) (not x7)))))
(check-sat)
