; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
(set-logic NIRA)
(declare-fun i8 () Int)
(declare-fun i12 () Int)
(declare-fun r11 () Real)
(declare-fun r18 () Real)
(declare-fun i19 () Int)
(push)
(assert (= 1 (* i8 (to_int r18))))
(check-sat)
(pop)
(assert (is_int (- r18)))
(check-sat)
(assert (and (< i12 i19) (< 0 (+ i12 2)) (= i19 (* 3 (to_int r11)))))
(check-sat)
