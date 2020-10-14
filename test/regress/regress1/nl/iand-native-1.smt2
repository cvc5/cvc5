; COMMAND-LINE: --iand-mode=value
; COMMAND-LINE: --iand-mode=sum --bvand-integer-granularity=1 --finite-model-find
; COMMAND-LINE: --iand-mode=sum --bvand-integer-granularity=2 --finite-model-find
; COMMAND-LINE: --iand-mode=sum --bvand-integer-granularity=4 --finite-model-find


; EXPECT: sat
(set-logic QF_NIA)
(set-info :status sat)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (and (<= 0 x) (< x 16)))
(assert (and (<= 0 y) (< y 16)))
(assert (> ((_ iand 4) x y) 0))

(check-sat)
