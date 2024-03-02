; COMMAND-LINE: --iand-mode=value
; COMMAND-LINE: --iand-mode=sum --bvand-integer-granularity=1
; COMMAND-LINE:  --solve-bv-as-int=iand --iand-mode=bitwise
; EXPECT: unsat
;; Logic not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic QF_NIA)
(set-info :status unsat)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (and (<= 0 x) (< x 16)))
(assert (and (<= 0 y) (< y 16)))
(assert (> ((_ iand 4) x y) 0))
(assert (= (* x y) 0))
(assert (= (+ x y) 15))

(check-sat)
