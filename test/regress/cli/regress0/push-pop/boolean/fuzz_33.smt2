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
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (not (and (not (not (and (and (not x3) (not x2)) (not (not x1))))) (or (not (and (not (not x5)) (and (and x3 x3) (and x0 x2)))) (or (or (not (not x0)) (or (or x1 x5) (not x2))) (not (or (or x4 x5) (not x4))))))))
(assert (not (or (not (not (and (not x5) (not x4)))) (or (and (and (and x5 x0) (not x2)) (and (or x1 x1) (or x3 x5))) (and (not (and x5 x0)) (or (not x0) (or x1 x2)))))))
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (or (not (and x4 x4)) (not (and x0 x4))))
(check-sat)
(push 1)
(assert (or (not x2) (not x2)))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (or (and (and (and x1 x0) (and x2 x5)) (or (and x3 x2) (or x1 x0))) (not (or (and x3 x1) (or x0 x1)))))
(check-sat)
