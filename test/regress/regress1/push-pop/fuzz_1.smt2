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
(assert (or (and (or (and (and (or (and (and (and x6 x1) (not x7)) (not (and x5 x9))) (or (or (and x8 x7) (or x5 x4)) (and (and x3 x2) (and x2 x9)))) (and (or (not (or x8 x3)) (and (or x1 x0) (not x9))) (or (or (and x7 x1) (not x5)) (not (and x1 x8))))) (not (and (and (or (and x4 x2) (or x5 x5)) (and (and x4 x6) (not x8))) (and (or (or x7 x4) (and x3 x1)) (or (and x8 x7) (or x9 x8)))))) (or (or (or (and (not (not x6)) (or (and x1 x5) (or x5 x2))) (or (not (or x3 x1)) (and (not x3) (or x0 x9)))) (and (or (not (or x0 x7)) (or (or x8 x3) (or x5 x9))) (or (or (not x3) (and x0 x5)) (and (or x7 x8) (or x6 x7))))) (not (not (not (and (and x0 x3) (and x1 x0))))))) (and (and (or (and (and (not (not x0)) (or (or x3 x4) (and x0 x9))) (not (not (and x1 x5)))) (not (not (or (and x7 x5) (not x0))))) (or (not (and (or (or x0 x9) (not x8)) (not (and x4 x5)))) (not (or (and (and x9 x3) (not x8)) (or (or x4 x9) (and x9 x7)))))) (and (or (not (and (not (not x8)) (or (not x8) (or x2 x1)))) (or (or (not (not x6)) (and (and x5 x2) (or x3 x8))) (not (and (or x7 x7) (or x5 x2))))) (or (or (and (not (not x2)) (and (or x2 x9) (or x8 x5))) (or (or (and x3 x4) (and x7 x5)) (and (not x1) (not x6)))) (or (or (and (not x4) (and x3 x3)) (and (not x5) (or x7 x9))) (not (and (not x8) (and x5 x0)))))))) (or (not (or (or (not (and (or (not x5) (and x0 x6)) (not (not x0)))) (and (not (or (or x5 x1) (or x4 x0))) (and (not (or x4 x9)) (or (or x4 x1) (or x7 x8))))) (or (or (not (or (and x2 x3) (and x1 x4))) (not (and (and x2 x3) (or x5 x7)))) (not (not (or (or x7 x9) (and x3 x5))))))) (not (not (or (not (or (or (not x0) (not x9)) (or (or x3 x9) (or x9 x1)))) (or (and (not (not x1)) (and (and x9 x3) (or x0 x8))) (or (and (and x3 x7) (or x6 x8)) (not (or x9 x1))))))))))
(check-sat)
(push 1)
(assert (and (not (or (not (or (not (not x3)) (and (and x2 x3) (and x9 x3)))) (or (or (or (and x5 x8) (and x4 x6)) (not (or x7 x3))) (not (and (or x8 x6) (and x4 x7)))))) (or (or (not (not (or (and x5 x1) (or x8 x3)))) (and (not (and (not x5) (not x1))) (or (not (not x0)) (not (not x6))))) (or (and (not (and (or x1 x2) (and x5 x4))) (and (not (and x3 x9)) (or (not x9) (not x7)))) (and (not (and (or x6 x2) (or x9 x9))) (or (and (not x9) (or x4 x4)) (not (and x4 x7))))))))
(check-sat)
(push 1)
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (not (not (not (and (not (and (or (not (not x7)) (or (and x6 x1) (not x6))) (or (and (or x4 x3) (not x3)) (or (or x4 x1) (not x4))))) (not (or (and (not (not x4)) (not (and x5 x6))) (not (and (or x2 x1) (or x3 x7))))))))))
(check-sat)
(push 1)
(assert (not (and (not (not x1)) (or (or x8 x7) (and x1 x2)))))
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(assert (not (or x6 x2)))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (or (and (not (and (and x3 x6) (and x6 x9))) (not (or (and x1 x6) (and x5 x1)))) (and (not (or (and x2 x8) (not x4))) (or (not (not x3)) (or (not x3) (or x1 x7))))))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (not (not (or (not (and (not (not (and (not (not x5)) (or (not x3) (or x1 x7))))) (not (or (or (or (and x8 x9) (or x6 x8)) (or (not x6) (not x2))) (not (and (not x8) (or x3 x9))))))) (or (and (and (and (and (and (and x7 x9) (and x3 x2)) (not (and x1 x4))) (and (not (not x1)) (and (or x8 x3) (or x3 x4)))) (and (and (or (and x4 x6) (and x9 x2)) (not (or x9 x1))) (not (and (or x6 x8) (not x2))))) (and (and (or (and (or x1 x2) (and x4 x8)) (or (or x7 x4) (or x3 x1))) (and (not (not x2)) (or (and x3 x0) (not x9)))) (not (not (not (not x1)))))) (and (or (not (not (or (or x2 x9) (or x8 x8)))) (or (or (not (and x5 x2)) (not (or x4 x5))) (and (not (or x6 x9)) (not (not x7))))) (not (and (not (not (or x5 x4))) (and (or (and x1 x7) (or x2 x2)) (not (not x9)))))))))))
(assert (not (or (and (or (or x6 x2) (and x9 x1)) (and (not x3) (and x8 x2))) (or (and (or x0 x0) (not x7)) (and (not x1) (and x7 x1))))))
(check-sat)
(pop 1)
(assert (and (or (not (or (or (or (not (not (and x9 x8))) (and (not (and x6 x4)) (and (or x6 x2) (and x4 x2)))) (and (or (and (and x1 x4) (and x1 x8)) (and (or x6 x0) (or x8 x6))) (or (and (not x8) (and x7 x6)) (or (not x5) (not x7))))) (and (or (or (not (or x5 x5)) (and (and x3 x8) (not x9))) (and (or (or x6 x6) (or x0 x6)) (or (and x5 x1) (not x9)))) (or (and (or (and x5 x6) (not x9)) (not (not x6))) (or (not (and x9 x3)) (not (not x1))))))) (and (and (or (and (and (and (and x6 x3) (or x5 x5)) (or (and x7 x8) (and x3 x6))) (and (and (not x2) (not x7)) (not (and x2 x2)))) (or (not (and (not x5) (not x5))) (and (and (not x7) (and x8 x2)) (not (and x9 x1))))) (or (not (or (and (not x9) (not x0)) (and (not x8) (and x8 x5)))) (not (not (not (not x5)))))) (or (not (or (or (or (not x4) (and x1 x3)) (or (and x6 x1) (not x5))) (not (not (not x4))))) (and (and (or (not (or x9 x8)) (or (not x0) (and x9 x5))) (and (not (not x4)) (not (or x5 x8)))) (and (and (or (and x2 x1) (not x3)) (and (and x5 x6) (not x8))) (not (or (not x1) (not x8)))))))) (and (or (and (and (or (or (and (or x1 x5) (not x3)) (and (not x9) (not x3))) (and (and (or x1 x0) (or x2 x8)) (or (not x7) (and x0 x7)))) (or (or (and (and x1 x7) (or x4 x1)) (and (or x4 x9) (and x3 x9))) (not (and (not x8) (and x4 x2))))) (and (or (and (or (or x9 x5) (not x7)) (or (or x8 x9) (or x6 x4))) (and (not (not x1)) (or (and x7 x3) (or x0 x7)))) (or (or (and (not x6) (not x2)) (and (not x1) (and x8 x0))) (not (or (and x1 x8) (and x7 x3)))))) (and (and (or (and (or (or x6 x3) (not x5)) (not (not x9))) (and (or (or x5 x0) (and x8 x5)) (and (and x7 x0) (and x0 x9)))) (not (or (and (and x9 x1) (and x6 x7)) (and (or x4 x3) (or x7 x4))))) (and (or (not (and (or x5 x4) (or x1 x4))) (not (and (or x3 x1) (or x2 x7)))) (not (and (or (or x0 x6) (not x4)) (and (or x0 x0) (not x1))))))) (and (not (and (not (not (and (not x9) (and x2 x1)))) (and (not (or (or x0 x1) (not x4))) (not (or (not x1) (not x1)))))) (not (or (not (or (not (or x4 x6)) (not (not x4)))) (and (or (and (not x7) (not x3)) (or (not x4) (or x3 x6))) (and (and (and x9 x9) (and x2 x2)) (not (or x8 x4))))))))))
(assert (and (and (or x9 x9) (or x2 x7)) (and (and x0 x3) (and x5 x2))))
(assert (and (and (or (or x2 x2) (or x5 x2)) (and (or x6 x3) (or x1 x8))) (or (not (or x6 x4)) (or (or x2 x7) (or x4 x4)))))
(check-sat)
(push 1)
