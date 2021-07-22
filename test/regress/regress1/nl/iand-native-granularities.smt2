; COMMAND-LINE: --iand-mode=value
; COMMAND-LINE: --iand-mode=sum --bvand-integer-granularity=1 --finite-model-find
; COMMAND-LINE: --iand-mode=bitwise
; COMMAND-LINE: --iand-mode=bitwise --bvand-integer-granularity=1
; COMMAND-LINE: --iand-mode=bitwise --bvand-integer-granularity=3
; COMMAND-LINE: --iand-mode=bitwise --bvand-integer-granularity=4
; EXPECT: unsat
(set-logic QF_NIA)
(set-info :status unsat)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (>= x 0))
(assert (>= y 0))

(assert (<= (+ x y) 32))

(assert (or
           (>= ((_ iand 5) x y) 32)
           (>= ((_ iand 6) x y) 32)))

(check-sat)