; COMMAND-LINE: --dump-difficulty
; SCRUBBER: sed 's/.*//g'
; EXIT: 0
(set-logic ALL)
(declare-const x Real)
(declare-const x1 Bool)
(declare-const p (_ BitVec 1))
(assert (= true (and (not (bvsmulo p ((_ int_to_bv 1) 0))) (= 0.0 (+ x (ite (> x 0.0) 0.0 11.3))) (= (ite x1 0.0 1.0) (+ x (ite (> x 0.0) 0.0 11.3))))))
(check-sat)
