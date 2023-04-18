; COMMAND-LINE: -o timeout-core-benchmark --timeout-core-timeout=500
; EXPECT: ;; timeout core
; EXPECT: (set-logic ALL)
; EXPECT: (declare-fun w () Int)
; EXPECT: (declare-fun x () Int)
; EXPECT: (declare-fun y () Int)
; EXPECT: (declare-fun u () Int)
; EXPECT: (assert (let ((_let_1 (* (- 1) (* y y y)))) (let ((_let_2 (* x x x))) (or (= _let_2 (+ 33 _let_1 (* (- 1) (* w w w)))) (= _let_2 (+ 33 _let_1 (* (- 1) (* u u u))))))))
; EXPECT: (check-sat)
; EXPECT: ;; end timeout core
; EXPECT: unknown
; EXPECT: (
; EXPECT: hard
; EXPECT: )
(set-logic ALL)
(define-fun triple ((x Int) (y Int) (z Int) (w Int)) Bool (= (+ (* x x x) (* y y y) (* z z z)) w))
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun w () Int)
(declare-fun u () Int)
(assert (! (> u 0) :named u0))
(assert (! (< w 0) :named w0))
(assert (! (or (triple x y w 33) (triple x y u 33)) :named hard))
(get-timeout-core)
