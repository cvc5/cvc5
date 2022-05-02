; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat

(set-logic QF_UFLIA)

(declare-fun _n () Int)
(declare-fun _f (Int) Bool)
(declare-fun _g (Int) Bool)

(assert (not (= _n 0)))

(push 1)
(assert (or (_g 1) (or (not (_g _n)) (not (_f _n)))))
(check-sat)
(pop 1)


(assert
  (or (and (_g _n) (_f _n))
      (not (or (not (_g _n)) (not (_f _n))))))



(assert (or  (not (_g _n)) (not (_g 0))))
(assert (or  (not (_g _n)) (_g 0)))

(check-sat)
