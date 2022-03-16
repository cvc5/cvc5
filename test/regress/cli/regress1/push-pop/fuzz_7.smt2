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
(declare-fun x8 () Bool)
(declare-fun x9 () Bool)
(assert (and (and (or (or (and (not (and (and (or x9 x6) (or x8 x9)) (not (not x2)))) (and (not (and (and x3 x1) (or x7 x0))) (or (and (or x6 x7) (not x2)) (or (or x8 x8) (not x0))))) (and (or (and (or (or x7 x5) (or x2 x8)) (not (not x3))) (and (and (and x2 x0) (and x1 x9)) (and (and x7 x5) (or x8 x5)))) (and (or (and (or x3 x6) (and x9 x4)) (or (not x8) (and x2 x6))) (not (and (not x7) (or x6 x1)))))) (not (or (or (and (and (and x6 x2) (or x5 x9)) (not (not x2))) (or (or (and x5 x0) (or x3 x0)) (or (or x6 x9) (not x5)))) (or (not (or (not x0) (or x7 x7))) (not (or (and x6 x1) (not x1))))))) (or (and (or (and (not (or (or x4 x2) (and x4 x3))) (or (not (or x1 x7)) (not (not x7)))) (or (or (or (or x3 x0) (and x0 x2)) (and (not x1) (or x3 x8))) (not (or (not x3) (or x3 x0))))) (or (not (or (and (and x3 x7) (not x2)) (or (not x6) (or x8 x9)))) (not (not (or (and x1 x2) (and x6 x3)))))) (and (or (or (not (and (not x3) (not x0))) (and (and (not x4) (and x6 x6)) (and (and x4 x1) (not x3)))) (and (and (or (or x9 x9) (not x5)) (or (and x3 x0) (and x3 x2))) (not (or (not x9) (not x7))))) (or (or (or (or (not x4) (and x0 x2)) (not (or x1 x7))) (and (and (or x1 x8) (and x1 x1)) (and (or x7 x7) (or x0 x1)))) (and (and (not (not x3)) (or (or x2 x0) (not x4))) (and (not (not x8)) (or (and x0 x0) (not x8)))))))) (or (not (or (and (and (not (not (and x1 x2))) (and (not (not x5)) (or (not x9) (and x2 x8)))) (and (or (or (or x7 x1) (not x7)) (not (not x8))) (or (not (and x9 x9)) (or (not x3) (and x0 x0))))) (and (not (not (not (and x6 x6)))) (or (or (and (or x6 x6) (and x0 x9)) (not (not x1))) (or (or (not x2) (or x3 x5)) (or (or x7 x5) (and x1 x0))))))) (not (not (or (or (not (and (and x9 x4) (not x7))) (and (not (and x3 x7)) (and (and x4 x4) (and x1 x0)))) (and (and (and (or x3 x7) (or x5 x7)) (not (not x3))) (not (or (not x7) (or x6 x4))))))))))
(check-sat)
(push 1)
(assert (not (or (or (and x3 x8) (or x4 x0)) (and (not x9) (and x6 x8)))))
(assert (not (and (and (or (or x9 x5) (and x4 x3)) (not (and x2 x9))) (and (or (and x3 x4) (not x4)) (and (and x0 x3) (or x6 x2))))))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (or (or (or (not x4) (and x9 x9)) (or (or x1 x5) (not x4))) (or (and (or x6 x0) (not x3)) (and (or x8 x7) (or x4 x4)))))
(check-sat)
(push 1)
(assert (or (and (and x9 x7) (or x8 x2)) (or (not x9) (or x6 x0))))
(check-sat)
(pop 1)
(assert (and (not (not (not (and (not (or (not x4) (not x2))) (and (and (and x3 x1) (and x0 x0)) (or (not x2) (not x4))))))) (or (or (not (or (not (not (and x9 x0))) (and (and (not x0) (and x4 x4)) (or (not x0) (not x7))))) (or (or (not (not (and x8 x1))) (or (or (and x1 x3) (and x4 x4)) (or (not x6) (not x7)))) (and (not (and (not x5) (not x1))) (not (and (not x1) (not x2)))))) (or (not (and (and (and (or x0 x8) (not x5)) (not (or x0 x8))) (not (not (not x1))))) (or (not (and (or (and x3 x2) (and x7 x2)) (and (or x6 x8) (not x1)))) (and (and (or (and x0 x6) (and x5 x4)) (and (and x0 x6) (and x1 x0))) (or (or (not x7) (and x2 x3)) (not (or x2 x9)))))))))
(check-sat)
(push 1)
(assert (and (or (and (not (not (and (and x0 x4) (and x6 x4)))) (not (not (and (not x5) (not x9))))) (not (and (or (or (or x0 x1) (or x5 x5)) (not (not x6))) (and (or (and x2 x3) (and x3 x7)) (not (and x3 x3)))))) (or (not (not (or (not (not x8)) (and (not x7) (not x8))))) (not (or (not (not (or x8 x4))) (and (not (or x7 x6)) (not (and x5 x5))))))))
(assert (not (or (and (and (or (or (or (and (not x4) (not x8)) (not (not x2))) (not (and (not x8) (or x6 x2)))) (not (not (or (and x7 x6) (and x0 x4))))) (or (or (not (not (and x3 x7))) (or (not (not x1)) (not (not x8)))) (and (not (or (not x6) (and x6 x8))) (or (and (not x4) (not x6)) (or (or x3 x1) (and x8 x3)))))) (or (and (not (or (not (and x7 x6)) (and (not x7) (and x5 x7)))) (not (and (not (and x6 x8)) (and (not x8) (not x5))))) (not (and (or (or (or x4 x0) (not x6)) (and (not x3) (not x8))) (not (and (not x1) (and x4 x9))))))) (and (or (and (and (and (and (and x9 x1) (not x9)) (or (or x5 x5) (not x7))) (or (and (not x5) (not x8)) (not (and x0 x1)))) (or (or (or (not x4) (or x1 x6)) (or (or x2 x0) (not x5))) (or (not (not x7)) (not (not x5))))) (or (and (not (or (and x1 x3) (or x1 x7))) (or (or (not x0) (not x6)) (or (not x9) (and x0 x0)))) (and (or (or (or x8 x1) (or x5 x8)) (or (or x1 x7) (and x2 x2))) (not (and (and x5 x9) (and x5 x8)))))) (or (not (and (and (and (or x4 x2) (and x8 x5)) (not (and x2 x2))) (not (not (not x3))))) (and (and (or (or (and x3 x3) (not x2)) (not (or x2 x6))) (or (and (and x9 x1) (not x1)) (not (and x6 x8)))) (not (not (or (not x2) (or x4 x1))))))))))
(assert (and (not x4) (not x3)))
(assert (and (or x8 x9) (not x1)))
(check-sat)
