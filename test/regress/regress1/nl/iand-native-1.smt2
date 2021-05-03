; COMMAND-LINE: --iand-mode=value
; COMMAND-LINE: --iand-mode=sum --bvand-integer-granularity=1 --finite-model-find
; COMMAND-LINE: --iand-mode=bitwise
; COMMAND-LINE: --iand-mode=bitwise --bvand-integer-granularity=1
; COMMAND-LINE: --iand-mode=bitwise --bvand-integer-granularity=2
; COMMAND-LINE: --iand-mode=bitwise --bvand-integer-granularity=4
; COMMAND-LINE: --iand-mode=bitwise --bvand-integer-granularity=5
; COMMAND-LINE: --iand-mode=bitwise --bvand-integer-granularity=6
; EXPECT: sat
(set-logic QF_NIA)
(set-info :status sat)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (and (<= 0 x) (< x 16)))
(assert (and (<= 0 y) (< y 16)))
(assert (> ((_ iand 4) x y) 0))

(check-sat)
