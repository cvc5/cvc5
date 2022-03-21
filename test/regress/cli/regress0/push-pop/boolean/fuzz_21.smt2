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
(assert (or (or (and (not (not (and (and x1 x3) (or x3 x1)))) (or (not (and (or x2 x0) (and x0 x1))) (or (not (or x2 x1)) (or (and x1 x3) (not x3))))) (not (not (or (or (and x3 x1) (not x0)) (and (and x1 x1) (or x0 x3)))))) (and (not (and (and (not (and x1 x3)) (or (or x0 x2) (not x2))) (or (or (or x0 x3) (and x3 x0)) (or (or x0 x3) (and x1 x0))))) (or (not (or (not (and x3 x1)) (and (and x0 x0) (and x1 x2)))) (not (or (or (not x0) (and x0 x2)) (and (or x0 x0) (and x3 x1))))))))
(check-sat)
(push 1)
(check-sat)
(pop 1)
(check-sat)
(push 1)
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (not (not (and x2 x0))))
(check-sat)
(pop 1)
(assert (not (not (not x1))))
(check-sat)
