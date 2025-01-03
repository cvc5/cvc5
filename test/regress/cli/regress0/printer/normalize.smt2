; COMMAND-LINE: -o normalize --preprocess-only 
; EXPECT: ;; normalize start
; EXPECT: (set-logic LIA)
; EXPECT: (declare-fun v00000000 () Int)
; EXPECT: (declare-fun v00000001 () Int)
; EXPECT: (declare-fun v00000002 () Int)
; EXPECT: (assert (<= (+ v00000000 (* 3 v00000001)) 5))
; EXPECT: (assert (>= (+ v00000000 (* 2 v00000002)) 5))
; EXPECT: (assert (>= (+ v00000002 (* 2 v00000000)) 5))
; EXPECT: (assert true)
; EXPECT: (check-sat)
; EXPECT: ;; normalize end
; EXPECT: unknown
(set-logic LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (>= (+ x (* 2 y)) 5))
(assert (>= (+ y (* 2 x)) 5))
(assert (<= (+ x (* 3 z)) 5))
(check-sat)