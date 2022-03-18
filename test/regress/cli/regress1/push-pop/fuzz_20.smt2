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
(declare-fun x9 () Bool)
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (not (and x7 x7)))
(check-sat)
(push 1)
(assert (or (or x0 x1) (not x7)))
(assert (not (and x6 x9)))
(assert (and (and (not (or x7 x5)) (or (or x3 x8) (or x5 x8))) (or (or (or x1 x5) (and x3 x6)) (or (and x2 x5) (or x1 x1)))))
(assert (or (not (or (not (not (not x9))) (and (or (and x2 x6) (and x2 x4)) (not (or x8 x2))))) (not (or (and (and (not x2) (not x3)) (and (or x0 x0) (and x7 x5))) (not (not (or x1 x9)))))))
(assert (or (or (not (or (and (not (and (or (or x6 x6) (and x0 x2)) (or (not x5) (not x3)))) (not (and (or (and x1 x2) (not x1)) (not (not x3))))) (or (not (not (or (or x9 x0) (not x6)))) (and (or (and (and x2 x6) (not x4)) (not (not x9))) (not (or (not x7) (or x4 x9))))))) (and (not (and (and (or (or (and x1 x2) (and x1 x5)) (and (not x7) (or x5 x1))) (or (not (and x0 x1)) (or (not x6) (not x1)))) (and (or (not (not x3)) (or (not x1) (not x2))) (or (and (and x4 x6) (not x4)) (and (or x1 x6) (or x2 x3)))))) (and (and (and (or (not (or x9 x9)) (not (or x7 x3))) (or (not (and x5 x3)) (not (not x8)))) (not (or (or (not x1) (or x4 x9)) (not (and x4 x0))))) (or (or (and (or (or x0 x7) (or x4 x4)) (or (or x5 x4) (and x0 x4))) (or (not (and x7 x3)) (or (and x8 x0) (or x7 x8)))) (not (not (and (not x9) (and x1 x9)))))))) (not (and (or (not (not (and (and (and x4 x1) (or x5 x1)) (and (or x5 x4) (not x5))))) (not (not (and (or (and x3 x7) (or x2 x7)) (or (or x5 x0) (or x7 x4)))))) (not (not (not (not (or (or x3 x0) (or x7 x7))))))))))
(check-sat)
(pop 1)
(assert (or (not (or (and (or (not (and (or x8 x0) (and x5 x2))) (not (not (or x6 x0)))) (not (and (or (or x6 x9) (and x5 x7)) (and (or x1 x7) (and x0 x0))))) (or (and (and (not (not x1)) (not (and x8 x5))) (and (and (and x5 x2) (and x7 x1)) (not (and x0 x0)))) (or (not (and (and x3 x5) (not x3))) (not (or (and x1 x0) (and x2 x4))))))) (not (and (and (and (not (or (not x4) (or x3 x7))) (not (not (not x3)))) (or (not (not (and x2 x1))) (and (or (not x6) (and x0 x8)) (not (not x3))))) (or (or (not (and (or x2 x5) (and x9 x8))) (or (or (and x2 x6) (not x3)) (not (and x7 x3)))) (or (or (not (or x6 x4)) (not (not x0))) (or (or (not x3) (or x6 x7)) (not (and x6 x7)))))))))
(check-sat)
(push 1)
(assert (or (and (or (and (or (or (and (not x5) (not x9)) (or (and x3 x6) (and x3 x4))) (not (or (not x5) (or x6 x4)))) (and (and (and (not x4) (not x1)) (not (and x6 x2))) (and (or (not x4) (not x8)) (or (and x1 x3) (not x6))))) (not (not (and (or (not x8) (and x9 x1)) (and (not x3) (or x9 x4)))))) (not (and (or (not (or (or x1 x8) (or x9 x5))) (not (not (or x8 x8)))) (and (not (not (and x2 x5))) (or (or (not x6) (or x1 x2)) (or (not x0) (and x8 x4))))))) (and (or (or (and (and (not (and x7 x8)) (or (or x8 x3) (or x5 x2))) (not (or (and x3 x0) (and x8 x1)))) (or (and (and (not x2) (and x2 x2)) (or (not x1) (and x6 x6))) (or (and (not x2) (or x6 x9)) (not (and x8 x3))))) (not (and (or (or (or x7 x1) (not x6)) (and (and x6 x5) (not x8))) (not (not (not x4)))))) (and (not (not (or (or (or x6 x5) (not x6)) (or (or x7 x8) (or x2 x2))))) (not (or (and (or (and x1 x3) (not x7)) (and (and x4 x9) (or x2 x2))) (or (not (or x9 x7)) (not (and x5 x2)))))))))
(assert (and (not (and (and (or x2 x3) (or x1 x6)) (and (and x3 x6) (or x0 x7)))) (not (or (or (or x4 x0) (and x3 x4)) (and (not x6) (or x5 x8))))))
(check-sat)
(push 1)
(assert (not (and (and (and x4 x6) (or x9 x4)) (or (and x1 x9) (not x1)))))
(check-sat)
(push 1)
(assert (or (not (and (or (and (not x2) (not x5)) (not (and x0 x5))) (not (and (and x2 x9) (and x2 x3))))) (not (not (and (not (or x7 x9)) (and (and x7 x4) (or x8 x3)))))))
(check-sat)
(pop 1)
(assert (not (or x0 x0)))
(assert (not (not (or (or (and (and (not (or (and (not x0) (not x1)) (and (and x4 x9) (and x3 x9)))) (not (or (not (or x9 x3)) (and (and x4 x2) (not x7))))) (and (not (and (or (not x1) (and x9 x5)) (not (or x9 x3)))) (and (or (and (or x6 x1) (or x6 x6)) (or (not x0) (not x0))) (or (and (not x3) (and x5 x7)) (not (and x9 x7)))))) (not (not (or (not (or (and x1 x0) (not x5))) (or (and (or x5 x5) (and x5 x7)) (and (and x1 x7) (and x4 x6))))))) (and (not (not (or (or (or (or x9 x0) (or x7 x3)) (or (not x0) (or x8 x0))) (and (or (and x3 x1) (or x4 x7)) (and (not x5) (and x0 x1)))))) (or (or (and (and (or (not x0) (not x2)) (not (and x3 x9))) (or (and (or x9 x6) (or x6 x0)) (or (not x6) (or x8 x0)))) (not (or (and (and x8 x6) (not x1)) (and (not x4) (or x5 x3))))) (or (or (or (or (and x2 x7) (and x5 x4)) (and (or x7 x5) (or x7 x8))) (and (not (and x7 x0)) (and (not x2) (not x0)))) (and (and (or (and x9 x6) (or x5 x9)) (not (or x8 x3))) (or (and (or x8 x4) (and x5 x2)) (or (or x5 x1) (and x5 x8)))))))))))
(assert (and (or (and (or (and (not (and x3 x6)) (or (and x1 x3) (not x2))) (and (not (not x7)) (and (not x1) (not x5)))) (not (not (not (or x6 x5))))) (or (and (or (not (and x2 x0)) (and (or x6 x8) (and x9 x2))) (or (not (and x7 x3)) (and (not x3) (or x7 x0)))) (not (or (not (not x2)) (or (or x3 x7) (not x9)))))) (and (not (or (and (not (or x9 x3)) (or (not x6) (and x1 x2))) (and (or (or x2 x3) (and x6 x7)) (and (and x2 x8) (and x5 x7))))) (not (or (not (and (not x0) (and x8 x1))) (not (not (or x7 x2))))))))
(check-sat)
