; COMMAND-LINE: --proof-check=eager
; EXPECT: sat
(set-logic QF_UFLRA)
(declare-fun v1 () Real)
(declare-fun v2 () Real)
(declare-fun f1 (Real) Real)
(declare-fun f0 (Real Real) Real)
(declare-fun p0 (Real Real) Bool)
(assert 
(ite 
  (or (= 0.0 v2) (> 1 (ite (< (- (- v1)) 1.0) 1.0 (ite (p0 0.0 v1) 0.0 1.0)))) 
  (= 0.0 (ite (= 1.0 (f1 0.0)) 0.0 (f1 1.0))) 
  (and 
    (= 1.0 (ite (= 0.0 (f1 1.0)) v2 (- 1.0))) 
    (=> (not (p0 0.0 (- (- (- v2))))) (= 1.0 (ite (= 1.0 v2) (ite (= 0 (f0 0.0 1.0)) 1.0 (f0 0.0 (- v2 (- v1)))) 0.0))))))
(check-sat)
