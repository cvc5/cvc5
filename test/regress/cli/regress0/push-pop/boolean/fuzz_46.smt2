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
(declare-fun x8 () Bool)
(assert (or (or (not (not x7)) (or (or x2 x5) (or x8 x5))) (and (or (and x7 x8) (not x3)) (and (or x5 x7) (or x5 x1)))))
(check-sat)
(push 1)
(check-sat)
(push 1)
(check-sat)
(push 1)
(check-sat)
(push 1)
(assert (or (or (or (not x3) (or x4 x0)) (not (not x1))) (and (not (not x1)) (and (or x6 x8) (and x0 x8)))))
(assert (and (not (and x7 x6)) (not (and x7 x8))))
(assert (or x6 x3))
(check-sat)
(push 1)
(check-sat)
(push 1)
(assert (not (not (not (or x1 x2)))))
(check-sat)
(pop 1)
(assert (or (or (and (not (not (or x8 x7))) (and (and (and x3 x8) (and x6 x0)) (not (and x1 x7)))) (or (or (not (not x4)) (or (and x0 x0) (and x6 x7))) (not (not (or x7 x5))))) (not (or (not (and (not x6) (not x1))) (or (or (and x3 x1) (not x6)) (or (and x5 x4) (not x4)))))))
(check-sat)
(push 1)
(assert (and (not x2) (not x5)))
(check-sat)
(push 1)
(assert (or (or (not (not (not (or (or (or x1 x5) (not x7)) (or (not x1) (or x4 x4)))))) (or (not (and (or (or (not x0) (or x8 x4)) (and (not x4) (or x5 x3))) (not (not (not x6))))) (not (or (and (or (or x4 x8) (not x8)) (and (or x8 x8) (or x6 x0))) (not (and (and x4 x0) (or x7 x5))))))) (or (not (or (and (and (not (and x1 x1)) (or (not x8) (not x5))) (and (not (and x0 x2)) (or (or x8 x4) (or x4 x6)))) (not (not (or (and x1 x7) (or x7 x0)))))) (not (not (and (and (and (or x4 x3) (or x0 x8)) (not (and x8 x7))) (or (or (not x1) (and x0 x5)) (and (or x8 x3) (and x4 x6)))))))))
(assert (or (and (and (not (not (and (or (not (and x3 x8)) (and (or x8 x0) (or x3 x5))) (not (or (or x7 x1) (and x6 x4)))))) (or (not (or (not (and (or x3 x8) (and x2 x1))) (and (not (or x6 x2)) (not (or x8 x6))))) (or (or (or (not (or x3 x6)) (not (not x1))) (or (or (and x4 x6) (or x6 x1)) (or (and x3 x3) (not x4)))) (or (or (and (or x0 x3) (or x6 x1)) (or (or x2 x5) (and x2 x4))) (or (not (not x1)) (not (or x5 x8))))))) (not (or (or (not (and (or (and x1 x4) (not x6)) (not (or x0 x7)))) (not (not (and (not x5) (or x4 x7))))) (or (and (and (not (or x8 x5)) (not (and x3 x6))) (and (and (not x1) (not x6)) (or (or x8 x8) (and x6 x1)))) (and (or (and (or x6 x5) (and x4 x6)) (or (or x1 x0) (or x1 x5))) (or (or (not x4) (not x3)) (not (or x1 x8)))))))) (not (or (and (and (not (or (not (or x3 x6)) (or (or x1 x1) (and x2 x0)))) (not (and (not (not x7)) (not (and x3 x4))))) (not (or (not (and (not x8) (not x5))) (and (or (not x6) (and x4 x3)) (not (not x2)))))) (and (or (not (not (or (or x1 x6) (not x5)))) (not (or (and (not x0) (and x1 x6)) (and (or x0 x5) (and x3 x0))))) (or (not (and (not (and x3 x7)) (and (or x0 x5) (and x1 x0)))) (and (or (not (not x3)) (and (or x7 x3) (or x8 x1))) (not (not (not x5))))))))))
(check-sat)
